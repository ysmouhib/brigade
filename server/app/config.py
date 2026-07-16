"""Runtime configuration, read once from environment variables."""
from __future__ import annotations
import os
from dataclasses import dataclass, field


def _b(name: str, default: bool = False) -> bool:
    return os.getenv(name, "1" if default else "0").lower() in ("1", "true", "yes")


@dataclass
class Config:
    # --- modes ---
    fake_llm: bool = field(default_factory=lambda: _b("FAKE_LLM"))
    lean_mode: str = field(default_factory=lambda: os.getenv("LEAN_MODE", "fake"))  # fake|file|repl
    # --- anthropic ---
    anthropic_api_key: str = field(default_factory=lambda: os.getenv("ANTHROPIC_API_KEY", ""))
    chef_model: str = field(default_factory=lambda: os.getenv("CHEF_MODEL", "claude-opus-4-8"))
    worker_model: str = field(default_factory=lambda: os.getenv("WORKER_MODEL", "claude-sonnet-4-6"))
    # --- lean ---
    lean_project_dir: str = field(default_factory=lambda: os.getenv("LEAN_PROJECT_DIR", "../lean/BrigadeLean"))
    lean_repl_bin: str = field(default_factory=lambda: os.getenv("LEAN_REPL_BIN", ""))
    lean_timeout_s: int = field(default_factory=lambda: int(os.getenv("LEAN_TIMEOUT_S", "180")))
    max_heartbeats: int = field(default_factory=lambda: int(os.getenv("LEAN_MAX_HEARTBEATS", "1000000")))
    # --- budgets (per job defaults; overridable per request) ---
    max_rounds: int = field(default_factory=lambda: int(os.getenv("MAX_ROUNDS", "2")))
    n_brainstormers: int = field(default_factory=lambda: int(os.getenv("N_BRAINSTORMERS", "3")))
    statement_retries: int = field(default_factory=lambda: int(os.getenv("STATEMENT_RETRIES", "3")))
    repair_cycles: int = field(default_factory=lambda: int(os.getenv("REPAIR_CYCLES", "4")))
    max_depth: int = field(default_factory=lambda: int(os.getenv("MAX_DEPTH", "2")))
    max_lean_calls: int = field(default_factory=lambda: int(os.getenv("MAX_LEAN_CALLS", "120")))
    max_llm_calls: int = field(default_factory=lambda: int(os.getenv("MAX_LLM_CALLS", "200")))
    # --- verification policy: 'full' checks every attempt individually;
    #     'strategic' adds per-lemma numeric probes and batches sibling proof checks ---
    verify_policy: str = field(default_factory=lambda: os.getenv("VERIFY_POLICY", "strategic"))
    # --- proving power ---
    tactic_cascade: bool = field(default_factory=lambda: _b("TACTIC_CASCADE", True))  # try omega/ring/simp/... before any LLM prover call
    prove_samples: int = field(default_factory=lambda: int(os.getenv("PROVE_SAMPLES", "1")))  # parallel proof candidates on the first attempt
    retrieval: str = field(default_factory=lambda: os.getenv("RETRIEVAL", "off"))  # off | loogle | leansearch
    # --- optional dedicated prover model (OpenAI-compatible endpoint, e.g. a local
    #     Goedel-Prover-V2 / DeepSeek-Prover-V2 served by vLLM); used for role=prover only ---
    prover_base_url: str = field(default_factory=lambda: os.getenv("PROVER_BASE_URL", ""))
    prover_model: str = field(default_factory=lambda: os.getenv("PROVER_MODEL", ""))
    prover_api_key: str = field(default_factory=lambda: os.getenv("PROVER_API_KEY", ""))
    # --- persistence: path to a SQLite file; empty keeps the in-memory-only store ---
    db_path: str = field(default_factory=lambda: os.getenv("BRIGADE_DB", ""))
    # --- server ---
    auth_token: str = field(default_factory=lambda: os.getenv("AUTH_TOKEN", ""))
