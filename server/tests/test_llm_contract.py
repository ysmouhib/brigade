"""Contract tests for the real Claude call path.

These run the actual `anthropic` SDK installed in this environment, with the network
replaced by an httpx MockTransport. They exist because every other test uses
ScriptedLLM, which is how a breaking SDK change (v1.0 removed `temperature`) went
unnoticed: real jobs failed on their first call while the suite stayed green.
"""
from __future__ import annotations
import json

import anthropic
import httpx2 as httpx  # the anthropic SDK v1+ is built on httpx2
import pytest

from app import llm as llm_mod
from app.llm import AnthropicLLM, complete_json


def _message(text: str) -> dict:
    # Shape of a Messages API response (see the Messages API reference).
    return {"id": "msg_test", "type": "message", "role": "assistant", "model": "claude-test",
            "content": [{"type": "text", "text": text}], "stop_reason": "end_turn",
            "stop_sequence": None, "usage": {"input_tokens": 12, "output_tokens": 7}}


class _Recorder:
    """Stands in for the network; records each request body."""

    def __init__(self, responses):
        self.responses = list(responses)
        self.bodies: list[dict] = []

    def __call__(self, request: httpx.Request) -> httpx.Response:
        self.bodies.append(json.loads(request.content))
        status, payload = self.responses.pop(0) if len(self.responses) > 1 else self.responses[0]
        return httpx.Response(status, json=payload)


@pytest.fixture
def wire(monkeypatch):
    """Route every AsyncAnthropic client the code creates through a recorder."""
    holder = {}
    real = anthropic.AsyncAnthropic

    def factory(*args, **kwargs):
        kwargs["http_client"] = httpx.AsyncClient(transport=httpx.MockTransport(holder["rec"]))
        kwargs.setdefault("max_retries", 0)
        kwargs["max_retries"] = 0   # keep tests fast and deterministic
        return real(*args, **kwargs)

    monkeypatch.setattr(anthropic, "AsyncAnthropic", factory)

    async def _no_sleep(*_a, **_k):
        return None
    monkeypatch.setattr(llm_mod.asyncio, "sleep", _no_sleep)

    def install(*responses):
        holder["rec"] = _Recorder(responses)
        return holder["rec"]
    return install


async def test_real_sdk_call_succeeds_and_sends_only_supported_parameters(wire):
    rec = wire((200, _message('{"ok": true}')))
    llm = AnthropicLLM("test-key", chef_model="chef-model", worker_model="worker-model")
    out = await complete_json(llm, role="skeptic", system="sys", user="hi", temperature=0.4)
    assert out == {"ok": True}
    body = rec.bodies[0]
    # SDK v1+ removed temperature/top_p/top_k, and Claude 4.7+ rejects non-default values.
    assert not {"temperature", "top_p", "top_k"} & set(body)
    assert body["model"] == "worker-model" and body["system"] == "sys"


async def test_roles_route_to_chef_and_worker_models(wire):
    rec = wire((200, _message("{}")))
    llm = AnthropicLLM("test-key", chef_model="chef-model", worker_model="worker-model")
    for role in ("chef", "strategist", "critic", "prover", "formalizer"):
        await llm.complete(role=role, system="s", user="u")
    assert [b["model"] for b in rec.bodies] == ["chef-model"] * 3 + ["worker-model"] * 2


async def test_request_errors_are_fatal_and_not_retried(wire):
    err = {"type": "error", "error": {"type": "invalid_request_error", "message": "bad model"}}
    rec = wire((400, err))
    llm = AnthropicLLM("test-key", chef_model="chef-model", worker_model="worker-model")
    with pytest.raises(llm_mod.LLMFatalError, match="400"):
        await llm.complete(role="chef", system="s", user="u")
    assert len(rec.bodies) == 1, "a 400 cannot succeed on retry"


async def test_overload_is_retried_then_reported_as_transient(wire):
    err = {"type": "error", "error": {"type": "overloaded_error", "message": "busy"}}
    rec = wire((529, err), (529, err), (200, _message("{}")))
    llm = AnthropicLLM("test-key", chef_model="chef-model", worker_model="worker-model")
    assert await llm.complete(role="chef", system="s", user="u") == "{}"
    assert len(rec.bodies) == 3

    rec = wire((529, err))   # overloaded on every attempt
    llm = AnthropicLLM("test-key", chef_model="chef-model", worker_model="worker-model")
    with pytest.raises(llm_mod.LLMError):
        await llm.complete(role="chef", system="s", user="u")
    assert len(rec.bodies) == llm.max_attempts
