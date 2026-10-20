"""Runtime configuration, read once from environment variables.

Values are read the way people write .env files: an inline `# comment` after whitespace
and surrounding quotes are ignored, whichever loader exported them. Mode switches accept
only their known values and integers must parse; anything else raises ValueError naming
the variable, so a typo stops startup instead of silently changing behavior.
"""
from __future__ import annotations
import os
import re
from dataclasses import dataclass, field
from pathlib import Path

_INLINE_COMMENT = re.compile(r"(?:^|\s)#.*$")

# Repository root: where .env and scripts/setup_lean.sh put things. The server itself
# runs from server/, so relative paths are resolved against this, not the working dir.
REPO_ROOT = Path(__file__).resolve().parents[2]

LEAN_MODES = ("fake", "file", "repl")
VERIFY_POLICIES = ("full", "strategic")
RETRIEVAL_BACKENDS = ("off", "loogle", "leansearch")
LLM_PROVIDERS = ("anthropic", "openai")


def _env(name: str, default: str = "") -> str:
    raw = os.getenv(name)
    if raw is None:
        return default
    val = _INLINE_COMMENT.sub("", raw).strip()
    if len(val) >= 2 and val[0] == val[-1] and val[0] in "\"'":
        val = val[1:-1]
    return val


def _repo_path(name: str, default: str = "") -> str:
    val = _env(name, default)
    if not val:
        return ""
    p = Path(val).expanduser()
    return str(p if p.is_absolute() else (REPO_ROOT / p).resolve())


def _b(name: str, default: bool = False) -> bool:
    return _env(name, "1" if default else "0").lower() in ("1", "true", "yes", "on")


def _int(name: str, default: int) -> int:
    val = _env(name, str(default))
    try:
        return int(val)
    except ValueError:
        raise ValueError(f"{name} must be an integer, got {val!r}") from None


def _choice(name: str, default: str, allowed: tuple[str, ...]) -> str:
    val = _env(name, default).lower()
    if val not in allowed:
        raise ValueError(f"{name}={val!r} is not one of {', '.join(allowed)}")
    return val


@dataclass
class Config:
    # --- modes ---
    fake_llm: bool = field(default_factory=lambda: _b("FAKE_LLM"))
    lean_mode: str = field(default_factory=lambda: _choice("LEAN_MODE", "fake", LEAN_MODES))
    # --- which API serves the agents: "anthropic" (Claude) or "openai" (any
    #     OpenAI-compatible endpoint, e.g. a free Gemini or Mistral tier) ---
    llm_provider: str = field(default_factory=lambda: _choice("LLM_PROVIDER", "anthropic", LLM_PROVIDERS))
    openai_base_url: str = field(default_factory=lambda: _env("OPENAI_BASE_URL"))
    openai_api_key: str = field(default_factory=lambda: _env("OPENAI_API_KEY"))
    # --- anthropic ---
    anthropic_api_key: str = field(default_factory=lambda: _env("ANTHROPIC_API_KEY"))
    chef_model: str = field(default_factory=lambda: _env("CHEF_MODEL", "claude-opus-4-8"))
    worker_model: str = field(default_factory=lambda: _env("WORKER_MODEL", "claude-sonnet-4-6"))
    # --- lean ---
    # paths relative to the repository root, as written in .env and by setup_lean.sh
    lean_project_dir: str = field(default_factory=lambda: _repo_path("LEAN_PROJECT_DIR", "lean/BrigadeLean"))
    lean_repl_bin: str = field(default_factory=lambda: _repo_path("LEAN_REPL_BIN"))
    lean_timeout_s: int = field(default_factory=lambda: _int("LEAN_TIMEOUT_S", 180))
    # one-time Mathlib load when the REPL starts (slow on a cold disk cache)
    lean_startup_timeout_s: int = field(default_factory=lambda: _int("LEAN_STARTUP_TIMEOUT_S", 1200))
    max_heartbeats: int = field(default_factory=lambda: _int("LEAN_MAX_HEARTBEATS", 1000000))
    # --- budgets (per job defaults; overridable per request) ---
    max_rounds: int = field(default_factory=lambda: _int("MAX_ROUNDS", 2))
    n_brainstormers: int = field(default_factory=lambda: _int("N_BRAINSTORMERS", 3))
    statement_retries: int = field(default_factory=lambda: _int("STATEMENT_RETRIES", 3))
    repair_cycles: int = field(default_factory=lambda: _int("REPAIR_CYCLES", 4))
    max_depth: int = field(default_factory=lambda: _int("MAX_DEPTH", 2))
    max_lean_calls: int = field(default_factory=lambda: _int("MAX_LEAN_CALLS", 120))
    max_llm_calls: int = field(default_factory=lambda: _int("MAX_LLM_CALLS", 200))
    # --- verification policy: 'full' checks every attempt individually;
    #     'strategic' adds per-lemma numeric probes and batches sibling proof checks ---
    verify_policy: str = field(default_factory=lambda: _choice("VERIFY_POLICY", "strategic", VERIFY_POLICIES))
    # --- proving power ---
    tactic_cascade: bool = field(default_factory=lambda: _b("TACTIC_CASCADE", True))  # try omega/ring/simp/... before any LLM prover call
    prove_samples: int = field(default_factory=lambda: _int("PROVE_SAMPLES", 1))  # parallel proof candidates on the first attempt
    retrieval: str = field(default_factory=lambda: _choice("RETRIEVAL", "off", RETRIEVAL_BACKENDS))
    # --- optional dedicated prover model (OpenAI-compatible endpoint, e.g. a local
    #     Goedel-Prover-V2 / DeepSeek-Prover-V2 served by vLLM); used for role=prover only ---
    prover_base_url: str = field(default_factory=lambda: _env("PROVER_BASE_URL"))
    prover_model: str = field(default_factory=lambda: _env("PROVER_MODEL"))
    prover_api_key: str = field(default_factory=lambda: _env("PROVER_API_KEY"))
    # --- persistence: path to a SQLite file; empty keeps the in-memory-only store ---
    db_path: str = field(default_factory=lambda: _env("BRIGADE_DB"))
    # --- server ---
    auth_token: str = field(default_factory=lambda: _env("AUTH_TOKEN"))
