"""Zero-dependency multi-provider LLM client (Gemini, OpenAI-compatible, Anthropic, or Scripted)."""

from __future__ import annotations

import asyncio
from dataclasses import dataclass
import json
import os
import re
from typing import Any, Callable, Protocol
import urllib.error
import urllib.request


class LLMError(RuntimeError):
    pass


class LLM(Protocol):
    async def complete(
        self,
        role: str,
        system: str,
        user: str,
        temperature: float = 0.3,
        max_tokens: int = 2000,
    ) -> str:
        ...


@dataclass
class ProviderConfig:
    provider: str = "auto"  # "gemini" | "openai" | "anthropic" | "auto"
    model: str = ""
    api_key: str = ""
    base_url: str = ""
    prover_model: str = ""
    prover_base_url: str = ""
    prover_api_key: str = ""
    timeout_s: float = 90.0

    @classmethod
    def from_env(cls) -> ProviderConfig:
        gemini_key = os.environ.get("GEMINI_API_KEY", "")
        openai_key = os.environ.get("OPENAI_API_KEY", "")
        anthropic_key = os.environ.get("ANTHROPIC_API_KEY", "")
        provider = os.environ.get("BRIGADE_PROVIDER", "auto").lower()
        if provider == "auto":
            if gemini_key:
                provider = "gemini"
            elif openai_key:
                provider = "openai"
            elif anthropic_key:
                provider = "anthropic"
            else:
                provider = "none"
        model = os.environ.get("BRIGADE_MODEL", "")
        if not model:
            model = {
                "gemini": "gemini-2.5-flash",
                "openai": "gpt-4.1",
                "anthropic": "claude-sonnet-4-20250514",
            }.get(provider, "")
        api_key = {
            "gemini": gemini_key,
            "openai": openai_key,
            "anthropic": anthropic_key,
        }.get(provider, "")
        return cls(
            provider=provider,
            model=model,
            api_key=api_key,
            base_url=os.environ.get("BRIGADE_BASE_URL", ""),
            prover_model=os.environ.get("PROVER_MODEL", ""),
            prover_base_url=os.environ.get("PROVER_BASE_URL", ""),
            prover_api_key=os.environ.get("PROVER_API_KEY", openai_key),
        )


def _http_post_json(url: str, headers: dict[str, str], payload: dict[str, Any], timeout_s: float) -> dict[str, Any]:
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")[:500]
        raise LLMError(f"HTTP {e.code} from {url}: {body}") from e
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
        raise LLMError(f"Request error to {url}: {e}") from e


class MultiProviderLLM:
    """Async multi-provider LLM client using stdlib HTTP (zero external SDK dependencies)."""

    def __init__(self, cfg: ProviderConfig):
        self.cfg = cfg

    async def complete(
        self,
        role: str,
        system: str,
        user: str,
        temperature: float = 0.3,
        max_tokens: int = 2000,
    ) -> str:
        # Optional dedicated prover routing (e.g., local Goedel-Prover / DeepSeek-Prover vLLM)
        if role == "prover" and self.cfg.prover_base_url and self.cfg.prover_model:
            return await asyncio.to_thread(
                self._call_openai,
                self.cfg.prover_base_url,
                self.cfg.prover_api_key,
                self.cfg.prover_model,
                system,
                user,
                temperature,
                max_tokens,
            )

        if self.cfg.provider == "none" or not self.cfg.api_key:
            raise LLMError(
                "No LLM API key configured (set GEMINI_API_KEY, OPENAI_API_KEY, or ANTHROPIC_API_KEY)."
            )

        if self.cfg.provider == "gemini":
            return await asyncio.to_thread(
                self._call_gemini, self.cfg.api_key, self.cfg.model, system, user, temperature, max_tokens
            )
        if self.cfg.provider == "openai":
            base = self.cfg.base_url or "https://api.openai.com/v1"
            return await asyncio.to_thread(
                self._call_openai, base, self.cfg.api_key, self.cfg.model, system, user, temperature, max_tokens
            )
        if self.cfg.provider == "anthropic":
            return await asyncio.to_thread(
                self._call_anthropic, self.cfg.api_key, self.cfg.model, system, user, temperature, max_tokens
            )
        raise LLMError(f"Unknown provider: {self.cfg.provider}")

    def _call_gemini(
        self, api_key: str, model: str, system: str, user: str, temperature: float, max_tokens: int
    ) -> str:
        url = (
            f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
            f"?key={api_key}"
        )
        payload = {
            "system_instruction": {"parts": [{"text": system}]},
            "contents": [{"role": "user", "parts": [{"text": user}]}],
            "generationConfig": {
                "temperature": temperature,
                "maxOutputTokens": max_tokens,
                "responseMimeType": "application/json",
            },
        }
        data = _http_post_json(url, {"Content-Type": "application/json"}, payload, self.cfg.timeout_s)
        cands = data.get("candidates") or []
        if not cands:
            raise LLMError(f"Gemini returned empty candidates: {data}")
        parts = cands[0].get("content", {}).get("parts", [])
        return "".join(p.get("text", "") for p in parts)

    def _call_openai(
        self, base_url: str, api_key: str, model: str, system: str, user: str, temperature: float, max_tokens: int
    ) -> str:
        url = base_url.rstrip("/") + "/chat/completions"
        headers = {"Content-Type": "application/json"}
        if api_key:
            headers["Authorization"] = f"Bearer {api_key}"
        payload = {
            "model": model,
            "temperature": temperature,
            "max_tokens": max_tokens,
            "messages": [
                {"role": "system", "content": system},
                {"role": "user", "content": user},
            ],
        }
        data = _http_post_json(url, headers, payload, self.cfg.timeout_s)
        choices = data.get("choices") or []
        if not choices:
            raise LLMError(f"OpenAI-compatible API returned no choices: {data}")
        return choices[0].get("message", {}).get("content", "")

    def _call_anthropic(
        self, api_key: str, model: str, system: str, user: str, temperature: float, max_tokens: int
    ) -> str:
        url = "https://api.anthropic.com/v1/messages"
        headers = {
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        }
        payload = {
            "model": model,
            "max_tokens": max_tokens,
            "temperature": temperature,
            "system": system,
            "messages": [{"role": "user", "content": user}],
        }
        data = _http_post_json(url, headers, payload, self.cfg.timeout_s)
        blocks = data.get("content") or []
        return "".join(b.get("text", "") for b in blocks if b.get("type") == "text")


class ScriptedLLM:
    """Deterministic test LLM returning scripted JSON payloads per role."""

    def __init__(self, handler: Callable[[str, str, str], dict[str, Any] | str]):
        self.handler = handler
        self.calls: list[tuple[str, str]] = []

    async def complete(
        self,
        role: str,
        system: str,
        user: str,
        temperature: float = 0.3,
        max_tokens: int = 2000,
    ) -> str:
        self.calls.append((role, user))
        out = self.handler(role, system, user)
        if isinstance(out, str):
            return out
        return json.dumps(out)


_FENCE_RE = re.compile(r"^```(?:json)?\s*|\s*```$", re.IGNORECASE)


def extract_json_object(raw: str) -> dict[str, Any]:
    text = raw.strip()
    text = _FENCE_RE.sub("", text).strip()
    try:
        obj = json.loads(text)
        if isinstance(obj, dict):
            return obj
    except json.JSONDecodeError:
        pass
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end != -1 and end > start:
        try:
            obj = json.loads(text[start : end + 1])
            if isinstance(obj, dict):
                return obj
        except json.JSONDecodeError as e:
            raise LLMError(f"Malformed JSON from LLM: {e}") from e
    raise LLMError(f"Expected JSON object from LLM, got: {raw[:200]}")


async def complete_json(
    llm: LLM,
    role: str,
    system: str,
    user: str,
    temperature: float = 0.3,
    max_tokens: int = 2000,
) -> dict[str, Any]:
    raw = await llm.complete(role, system, user, temperature=temperature, max_tokens=max_tokens)
    return extract_json_object(raw)
