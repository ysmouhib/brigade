"""LLM abstraction: a real Anthropic client and a scriptable fake for tests/demo.

Every agent call goes through `LLM.complete(role, system, user, ...)` and expects a JSON
object back; `extract_json` tolerates markdown fences and stray prose around the object.
"""
from __future__ import annotations
import asyncio
import json
import re
from typing import Protocol


class LLM(Protocol):
    async def complete(self, *, role: str, system: str, user: str,
                       temperature: float = 0.3, max_tokens: int = 2000,
                       model: str | None = None) -> str: ...


class LLMError(Exception):
    pass


def extract_json(text: str) -> dict:
    """Pull the first JSON object out of an LLM reply (fenced or bare)."""
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
    candidates = [fence.group(1)] if fence else []
    # bare object: first '{' to the matching last '}'
    start = text.find("{")
    if start != -1:
        depth = 0
        for i in range(start, len(text)):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    candidates.append(text[start:i + 1])
                    break
    for c in candidates:
        try:
            return json.loads(c)
        except json.JSONDecodeError:
            try:  # cheap repair: trailing commas
                return json.loads(re.sub(r",\s*([}\]])", r"\1", c))
            except json.JSONDecodeError:
                continue
    raise LLMError(f"no JSON object found in reply: {text[:200]!r}")


async def complete_json(llm: LLM, *, role: str, system: str, user: str,
                        temperature: float = 0.3, max_tokens: int = 2000,
                        model: str | None = None, retries: int = 2) -> dict:
    last: Exception | None = None
    for attempt in range(retries + 1):
        text = await llm.complete(role=role, system=system, user=user,
                                  temperature=temperature, max_tokens=max_tokens, model=model)
        try:
            return extract_json(text)
        except LLMError as e:
            last = e
            user = user + "\n\nYour previous reply was not valid JSON. Reply with ONLY one JSON object."
    raise LLMError(f"gave up parsing JSON after {retries + 1} attempts: {last}")


class AnthropicLLM:
    """Thin async wrapper over the Anthropic Messages API (see https://docs.claude.com/en/api/overview)."""

    def __init__(self, api_key: str, chef_model: str, worker_model: str):
        import anthropic  # imported lazily so tests never require the package config
        self._client = anthropic.AsyncAnthropic(api_key=api_key)
        self.chef_model = chef_model
        self.worker_model = worker_model
        self._sem = asyncio.Semaphore(4)  # basic concurrency cap

    def _model_for(self, role: str, override: str | None) -> str:
        if override:
            return override
        return self.chef_model if role in ("chef", "strategist", "critic") else self.worker_model

    async def complete(self, *, role: str, system: str, user: str,
                       temperature: float = 0.3, max_tokens: int = 2000,
                       model: str | None = None) -> str:
        import anthropic
        async with self._sem:
            for attempt in range(3):
                try:
                    msg = await self._client.messages.create(
                        model=self._model_for(role, model),
                        max_tokens=max_tokens,
                        temperature=temperature,
                        system=system,
                        messages=[{"role": "user", "content": user}],
                    )
                    return "".join(b.text for b in msg.content if getattr(b, "type", "") == "text")
                except (anthropic.RateLimitError, anthropic.APIStatusError, anthropic.APIConnectionError):
                    if attempt == 2:
                        raise
                    await asyncio.sleep(2.0 * (attempt + 1))
        raise LLMError("unreachable")


class OpenAICompatLLM:
    """Chat-completions client for any OpenAI-compatible endpoint (vLLM, llama.cpp, hosted).

    Lets a dedicated prover model — e.g. Goedel-Prover-V2 or DeepSeek-Prover-V2 served
    locally — take the prover role while a general model keeps the reasoning roles.
    """

    def __init__(self, base_url: str, model: str, api_key: str = ""):
        import httpx
        self.base_url = base_url.rstrip("/")
        self.model = model
        self._client = httpx.AsyncClient(
            timeout=httpx.Timeout(180.0),
            headers={"Authorization": f"Bearer {api_key}"} if api_key else {})

    async def complete(self, *, role: str, system: str, user: str,
                       temperature: float = 0.3, max_tokens: int = 2000,
                       model: str | None = None) -> str:
        r = await self._client.post(f"{self.base_url}/chat/completions", json={
            "model": model or self.model,
            "temperature": temperature,
            "max_tokens": max_tokens,
            "messages": [{"role": "system", "content": system},
                         {"role": "user", "content": user}],
        })
        r.raise_for_status()
        data = r.json()
        try:
            return data["choices"][0]["message"]["content"] or ""
        except (KeyError, IndexError, TypeError) as e:
            raise LLMError(f"unexpected chat-completions shape: {e}: {str(data)[:200]}")


class RoutedLLM:
    """Route the prover role to a dedicated model; everything else to the primary."""

    def __init__(self, primary: LLM, prover: LLM):
        self.primary, self.prover = primary, prover

    async def complete(self, *, role: str, system: str, user: str,
                       temperature: float = 0.3, max_tokens: int = 2000,
                       model: str | None = None) -> str:
        target = self.prover if role == "prover" else self.primary
        return await target.complete(role=role, system=system, user=user,
                                     temperature=temperature, max_tokens=max_tokens, model=model)


class ScriptedLLM:
    """Deterministic fake: dispatches to a handler(role, user, call_index) -> str."""

    def __init__(self, handler):
        self._handler = handler
        self._counts: dict[str, int] = {}

    async def complete(self, *, role: str, system: str, user: str,
                       temperature: float = 0.3, max_tokens: int = 2000,
                       model: str | None = None) -> str:
        key = role
        n = self._counts.get(key, 0)
        self._counts[key] = n + 1
        out = self._handler(role, user, n)
        if out is None:
            raise LLMError(f"ScriptedLLM has no reply for role={role!r} call #{n}")
        return out
