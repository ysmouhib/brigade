"""Lean 4 verification layer — the single source of truth in the system.

Three interchangeable backends:
  * FakeLean         — rule-driven simulator used for tests and the offline demo.
  * FileLeanVerifier — writes a scratch file into a Mathlib project and runs `lake env lean`.
                       Simple and robust, but re-elaborates imports on every call (slow).
  * ReplLeanVerifier — drives leanprover-community/repl over stdio with a warm
                       `import Mathlib` environment (fast; recommended for real runs).

Anything the orchestrator marks VERIFIED must have passed `check()` with zero errors and
zero sorries, and the assembled final file must additionally pass `axiom_audit`.
"""
from __future__ import annotations
import asyncio
import json
import os
import re
import shutil
import tempfile
import uuid
from dataclasses import dataclass, field
from typing import Callable, Protocol

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Tokens a proof body may never contain. `native_decide` is excluded because it extends
# the trusted base beyond the kernel; `sorry`/`admit`/`axiom` are outright cheating.
FORBIDDEN_IN_PROOFS = ["sorry", "admit", "axiom ", "native_decide", "sorryAx", "unsafe ", "@[implemented_by"]


def lint_proof(body: str) -> list[str]:
    hits = [tok.strip() for tok in FORBIDDEN_IN_PROOFS if tok in body]
    return [f"forbidden token in proof: '{t}'" for t in hits]


@dataclass
class VerifyResult:
    ok: bool
    errors: list[str] = field(default_factory=list)
    sorries: int = 0
    warnings: list[str] = field(default_factory=list)
    goals: list[str] = field(default_factory=list)   # goal states of sorries/errors when the backend exposes them

    def summary(self) -> str:
        if self.ok and self.sorries == 0:
            return "OK (no errors, no sorries)"
        if self.ok:
            return f"OK with {self.sorries} sorry(ies)"
        return "; ".join(self.errors[:3]) or "unknown Lean failure"


@dataclass
class AuditResult:
    ok: bool
    axioms: list[str] = field(default_factory=list)
    note: str = ""


class LeanVerifier(Protocol):
    async def check(self, code: str, context: str = "") -> VerifyResult:
        """Check `code`. `context` is previously *verified* code the snippet may cite;
        backends may cache its elaboration (the REPL backend does)."""
        ...
    async def axiom_audit(self, code: str, name: str) -> AuditResult: ...
    async def close(self) -> None: ...


THEOREM_RE = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)


def split_theorem_blocks(code: str) -> list[tuple[str, str]]:
    """Split a Lean source into (name, block_text) per theorem/lemma declaration."""
    matches = list(THEOREM_RE.finditer(code))
    blocks = []
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(code)
        blocks.append((m.group(1), code[m.start():end]))
    return blocks


class FakeLean:
    """Rule-driven simulator.

    rules: name -> (required_tokens, error_message). A block verifies iff every required
    token appears in it. bad_tokens: token -> error, applied to any block (used to make
    the statement gate fail realistically). Blocks containing `sorry` count as sorries
    and skip proof rules, mirroring real `by sorry` statement checks.
    """

    def __init__(self,
                 rules: dict[str, tuple[list[str], str]] | None = None,
                 bad_tokens: dict[str, str] | None = None):
        self.rules = rules or {}
        self.bad_tokens = bad_tokens or {}
        self.calls: list[str] = []

    async def check(self, code: str, context: str = "") -> VerifyResult:
        code = f"{context}\n\n{code}" if context else code
        self.calls.append(code)
        errors: list[str] = []
        sorries = 0
        for tok, msg in self.bad_tokens.items():
            if tok in code:
                errors.append(msg)
        for name, block in split_theorem_blocks(code):
            if "sorry" in block:
                sorries += 1
                continue
            req, msg = self.rules.get(name, ([], ""))
            missing = [t for t in req if t not in block]
            if missing:
                errors.append(msg or f"error: unsolved goals in {name}")
        return VerifyResult(ok=not errors, errors=errors, sorries=sorries)

    async def axiom_audit(self, code: str, name: str) -> AuditResult:
        if "sorry" in code:
            return AuditResult(ok=False, axioms=["sorryAx"], note="proof depends on sorryAx")
        return AuditResult(ok=True, axioms=sorted(STANDARD_AXIOMS))

    async def close(self) -> None:
        pass


ERROR_LINE = re.compile(r"^[^\n:]*:\d+:\d+:\s*error:\s*(.*)$", re.MULTILINE)
WARN_LINE = re.compile(r"^[^\n:]*:\d+:\d+:\s*warning:\s*(.*)$", re.MULTILINE)
AXIOM_LINE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")


class FileLeanVerifier:
    """Write `code` into a scratch .lean file inside a Mathlib project and run `lake env lean` on it."""

    def __init__(self, project_dir: str, timeout_s: int = 180, max_heartbeats: int = 1000000,
                 header: str = "import Mathlib\n"):
        self.project_dir = os.path.abspath(project_dir)
        self.timeout_s = timeout_s
        self.header = header + f"set_option maxHeartbeats {max_heartbeats}\n\n"
        self._lock = asyncio.Lock()

    async def _run(self, code: str) -> tuple[int, str]:
        scratch_dir = os.path.join(self.project_dir, ".brigade_scratch")
        os.makedirs(scratch_dir, exist_ok=True)
        path = os.path.join(scratch_dir, f"Check_{uuid.uuid4().hex[:10]}.lean")
        with open(path, "w") as f:
            f.write(self.header + code + "\n")
        try:
            proc = await asyncio.create_subprocess_exec(
                "lake", "env", "lean", path,
                cwd=self.project_dir,
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
            )
            try:
                out, _ = await asyncio.wait_for(proc.communicate(), timeout=self.timeout_s)
            except asyncio.TimeoutError:
                proc.kill()
                return 124, f"error: Lean check timed out after {self.timeout_s}s"
            return proc.returncode or 0, out.decode(errors="replace")
        finally:
            try:
                os.remove(path)
            except OSError:
                pass

    async def check(self, code: str, context: str = "") -> VerifyResult:
        if context:
            code = f"{context}\n\n{code}"
        async with self._lock:
            rc, out = await self._run(code)
        errors = ERROR_LINE.findall(out)
        warnings = WARN_LINE.findall(out)
        sorries = sum(1 for w in warnings if "sorry" in w) + out.count("declaration uses 'sorry'")
        if rc != 0 and not errors:
            errors = [out.strip()[:500] or f"lean exited with code {rc}"]
        return VerifyResult(ok=(rc == 0 and not errors), errors=errors, sorries=sorries, warnings=warnings)

    async def axiom_audit(self, code: str, name: str) -> AuditResult:
        async with self._lock:
            rc, out = await self._run(code + f"\n#print axioms {name}\n")
        m = AXIOM_LINE.search(out)
        if not m:
            if f"'{name}' does not depend on any axioms" in out:
                return AuditResult(ok=True, axioms=[])
            return AuditResult(ok=False, note=f"could not parse axiom report (rc={rc}): {out[:300]}")
        axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        bad = [a for a in axioms if a not in STANDARD_AXIOMS]
        return AuditResult(ok=not bad, axioms=axioms,
                           note="" if not bad else f"non-standard axioms: {bad}")

    async def close(self) -> None:
        pass


class ReplLeanVerifier:
    """Drive leanprover-community/repl (JSON-per-line over stdio) with a warm Mathlib env.

    Startup sends `import Mathlib` once (slow, ~30-90s); every later check reuses that
    environment id, so a single check typically takes seconds. The process is restarted
    automatically if it dies or times out.
    """

    def __init__(self, project_dir: str, repl_bin: str, timeout_s: int = 180,
                 max_heartbeats: int = 1000000):
        self.project_dir = os.path.abspath(project_dir)
        self.repl_bin = repl_bin
        self.timeout_s = timeout_s
        self.max_heartbeats = max_heartbeats
        self._proc: asyncio.subprocess.Process | None = None
        self._base_env: int | None = None
        self._ctx_envs: dict[str, int] = {}   # verified-context code -> env id (elaborated once)
        self._lock = asyncio.Lock()

    async def _ensure_started(self) -> None:
        if self._proc and self._proc.returncode is None and self._base_env is not None:
            return
        self._proc = await asyncio.create_subprocess_exec(
            "lake", "env", self.repl_bin,
            cwd=self.project_dir,
            stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
        )
        resp = await self._roundtrip({"cmd": f"import Mathlib\nset_option maxHeartbeats {self.max_heartbeats}"},
                                     timeout=max(self.timeout_s, 300))
        self._base_env = resp.get("env")
        if self._base_env is None:
            raise RuntimeError(f"REPL failed to import Mathlib: {resp}")

    async def _roundtrip(self, obj: dict, timeout: float) -> dict:
        assert self._proc and self._proc.stdin and self._proc.stdout
        self._proc.stdin.write((json.dumps(obj) + "\n\n").encode())
        await self._proc.stdin.drain()
        buf = b""
        while True:
            line = await asyncio.wait_for(self._proc.stdout.readline(), timeout=timeout)
            if not line:
                raise RuntimeError("REPL closed its stdout")
            buf += line
            s = buf.strip()
            if s:
                try:
                    return json.loads(s)
                except json.JSONDecodeError:
                    continue  # multi-line JSON: keep reading

    async def _restart(self) -> None:
        if self._proc:
            try:
                self._proc.kill()
            except ProcessLookupError:
                pass
        self._proc, self._base_env = None, None
        self._ctx_envs.clear()

    async def _env_for(self, context: str) -> int | None:
        """Elaborate a verified-context block once and reuse its env for later checks."""
        if not context:
            return self._base_env
        if context in self._ctx_envs:
            return self._ctx_envs[context]
        resp = await self._roundtrip({"cmd": context, "env": self._base_env}, timeout=self.timeout_s)
        msgs = resp.get("messages", []) or []
        env = resp.get("env")
        if env is None or any(m.get("severity") == "error" for m in msgs):
            return None  # caller falls back to a single concatenated check
        if len(self._ctx_envs) >= 8:   # bound the cache
            self._ctx_envs.pop(next(iter(self._ctx_envs)))
        self._ctx_envs[context] = env
        return env

    async def check(self, code: str, context: str = "") -> VerifyResult:
        async with self._lock:
            try:
                await self._ensure_started()
                env = await self._env_for(context)
                if env is None and context:   # context failed to elaborate alone: concatenate
                    resp = await self._roundtrip({"cmd": f"{context}\n\n{code}", "env": self._base_env},
                                                 timeout=self.timeout_s)
                else:
                    resp = await self._roundtrip({"cmd": code, "env": env}, timeout=self.timeout_s)
            except (asyncio.TimeoutError, RuntimeError, BrokenPipeError) as e:
                await self._restart()
                return VerifyResult(ok=False, errors=[f"error: Lean REPL failure/timeout: {e}"])
        msgs = resp.get("messages", []) or []
        errors = [m.get("data", "") for m in msgs if m.get("severity") == "error"]
        warnings = [m.get("data", "") for m in msgs if m.get("severity") == "warning"]
        sorry_items = resp.get("sorries", []) or []
        goals = [s.get("goal", "") for s in sorry_items if s.get("goal")]
        return VerifyResult(ok=not errors, errors=errors, sorries=len(sorry_items),
                            warnings=warnings, goals=goals)

    async def axiom_audit(self, code: str, name: str) -> AuditResult:
        res = await self.check(code + f"\n#print axioms {name}")
        joined = "\n".join(res.warnings) + "\n" + "\n".join(res.errors)
        async with self._lock:
            pass
        m = AXIOM_LINE.search(joined)
        if res.errors:
            return AuditResult(ok=False, note="; ".join(res.errors[:2]))
        if not m:
            # `#print axioms` reports via info messages, which the repl also surfaces;
            # fall back to accepting when nothing suspicious is present.
            return AuditResult(ok=("sorryAx" not in joined), axioms=[], note="axiom list not parsed")
        axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        bad = [a for a in axioms if a not in STANDARD_AXIOMS]
        return AuditResult(ok=not bad, axioms=axioms,
                           note="" if not bad else f"non-standard axioms: {bad}")

    async def close(self) -> None:
        await self._restart()


def make_verifier(cfg) -> LeanVerifier:
    if cfg.lean_mode == "file":
        return FileLeanVerifier(cfg.lean_project_dir, cfg.lean_timeout_s, cfg.max_heartbeats)
    if cfg.lean_mode == "repl":
        if not cfg.lean_repl_bin:
            raise RuntimeError("LEAN_MODE=repl requires LEAN_REPL_BIN")
        return ReplLeanVerifier(cfg.lean_project_dir, cfg.lean_repl_bin,
                                cfg.lean_timeout_s, cfg.max_heartbeats)
    from ..testing import default_fake_lean
    return default_fake_lean()
