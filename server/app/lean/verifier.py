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
import time
import uuid
from dataclasses import dataclass, field
from typing import Callable, Protocol

from ..progress import log

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
    infos: list[str] = field(default_factory=list)   # informational output, e.g. `#print axioms`

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
# Any other positioned message is informational (`trace`, `#print`); depending on the
# Lean version it is printed with or without an "info:" prefix.
POS_LINE = re.compile(r"^[^\n:]*:\d+:\d+:\s*(.*)$", re.MULTILINE)
AXIOM_LINE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")


def parse_lean_output(rc: int, out: str) -> VerifyResult:
    """Interpret the exit code and combined output of `lake env lean <file>`."""
    errors = ERROR_LINE.findall(out)
    warnings = WARN_LINE.findall(out)
    # Any warning mentioning sorry counts (the wording has varied across Lean versions);
    # erring this way can only reject a proof, never accept one.
    sorries = sum(1 for w in warnings if "sorry" in w)
    infos = [re.sub(r"^info:\s*", "", m) for m in POS_LINE.findall(out)
             if not m.startswith(("error:", "warning:"))]
    if rc != 0 and not errors:
        errors = [out.strip()[:500] or f"lean exited with code {rc}"]
    return VerifyResult(ok=(rc == 0 and not errors), errors=errors, sorries=sorries,
                        warnings=warnings, infos=infos)


def parse_axiom_report(rc: int, out: str, name: str) -> AuditResult:
    """Interpret `#print axioms <name>` output; anything unexpected fails closed."""
    errors = ERROR_LINE.findall(out)
    if errors:
        return AuditResult(ok=False, note="; ".join(errors[:2]))
    m = AXIOM_LINE.search(out)
    if m:
        axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        bad = [a for a in axioms if a not in STANDARD_AXIOMS]
        return AuditResult(ok=not bad, axioms=axioms,
                           note="" if not bad else f"non-standard axioms: {bad}")
    if f"'{name}' does not depend on any axioms" in out:
        return AuditResult(ok=True, axioms=[])
    return AuditResult(ok=False, note=f"could not parse axiom report (rc={rc}): {out[:300]}")


async def spawn_process_group(*args, **kw) -> asyncio.subprocess.Process:
    """Start a process in its own process group, so kill_process_tree can stop it and
    everything it started (`lake env X` runs X as a child of lake)."""
    if os.name == "posix":
        kw["start_new_session"] = True
    return await asyncio.create_subprocess_exec(*args, **kw)


async def kill_process_tree(proc) -> None:
    """Kill a process started by spawn_process_group together with its children."""
    pid = getattr(proc, "pid", -1) if proc is not None else -1
    if pid is None or pid <= 0:
        return
    try:
        if os.name == "posix":
            import signal
            os.killpg(pid, signal.SIGKILL)
        else:   # Windows: /T takes the child processes along
            import subprocess
            subprocess.run(["taskkill", "/F", "/T", "/PID", str(pid)], capture_output=True)
    except (ProcessLookupError, PermissionError, OSError):
        pass
    try:
        await asyncio.wait_for(proc.wait(), timeout=5)
    except Exception:  # noqa: BLE001 - already gone or not waitable
        pass


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
        with open(path, "w", encoding="utf-8") as f:   # Lean source is UTF-8 (ℕ, ∀, ...)
            f.write(self.header + code + "\n")
        try:
            proc = await spawn_process_group(
                "lake", "env", "lean", path,
                cwd=self.project_dir,
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
            )
            try:
                out, _ = await asyncio.wait_for(proc.communicate(), timeout=self.timeout_s)
            except asyncio.TimeoutError:
                await kill_process_tree(proc)
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
        t0 = time.monotonic()
        log.info("-> Lean (file): checking")
        async with self._lock:
            rc, out = await self._run(code)
        res = parse_lean_output(rc, out)
        log.info("<- Lean (file): %s in %.0fs", res.summary()[:80], time.monotonic() - t0)
        return res

    async def axiom_audit(self, code: str, name: str) -> AuditResult:
        async with self._lock:
            rc, out = await self._run(code + f"\n#print axioms {name}\n")
        return parse_axiom_report(rc, out, name)

    async def close(self) -> None:
        pass


class ReplLeanVerifier:
    """Drive leanprover-community/repl (JSON-per-line over stdio) with a warm Mathlib env.

    Startup sends `import Mathlib` once (slow, ~30-90s); every later check reuses that
    environment id, so a single check typically takes seconds. The process is restarted
    automatically if it dies or times out.
    """

    def __init__(self, project_dir: str, repl_bin: str, timeout_s: int = 180,
                 max_heartbeats: int = 1000000, startup_timeout_s: int = 1200):
        self.project_dir = os.path.abspath(project_dir)
        self.repl_bin = repl_bin
        self.timeout_s = timeout_s
        # Loading Mathlib reads ~5 GB of compiled files once; on a cold disk cache (e.g.
        # in WSL) it can take minutes. Every later check reuses the loaded environment.
        self.startup_timeout_s = startup_timeout_s
        self.max_heartbeats = max_heartbeats
        self._proc: asyncio.subprocess.Process | None = None
        self._base_env: int | None = None
        self._ctx_envs: dict[str, int] = {}   # verified-context code -> env id (elaborated once)
        self._lock = asyncio.Lock()

    async def _ensure_started(self) -> None:
        if self._proc and self._proc.returncode is None and self._base_env is not None:
            return
        t0 = time.monotonic()
        log.info("-> Lean REPL: starting and loading Mathlib (once per server start; "
                 "allowing up to %d min)", self.startup_timeout_s // 60)
        await self._spawn()
        resp = await self._roundtrip({"cmd": f"import Mathlib\nset_option maxHeartbeats {self.max_heartbeats}"},
                                     timeout=self.startup_timeout_s)
        self._base_env = resp.get("env")
        if self._base_env is None:
            raise RuntimeError(f"REPL failed to import Mathlib: {resp}")
        log.info("<- Lean REPL: ready in %.0fs", time.monotonic() - t0)

    async def _spawn(self) -> None:
        self._proc = await spawn_process_group(
            "lake", "env", self.repl_bin,
            cwd=self.project_dir,
            stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
            limit=2 ** 24,   # one REPL reply line can exceed asyncio's 64 KiB default
        )

    @property
    def ready(self) -> bool:
        """True once Mathlib is loaded and checks will be fast."""
        return self._base_env is not None and self._proc is not None

    async def warm_up(self) -> None:
        """Load Mathlib now (called at server start) instead of inside the first job."""
        async with self._lock:
            try:
                await self._ensure_started()
            except (asyncio.TimeoutError, RuntimeError, BrokenPipeError, OSError) as e:
                log.info("<- Lean REPL: could not load Mathlib: %s", e or type(e).__name__)
                await self._restart()

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
        proc, self._proc, self._base_env = self._proc, None, None
        await kill_process_tree(proc)   # the REPL itself, not just the `lake` wrapper
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
        res = await self._check(code, context)
        log.info("<- Lean REPL: %s", res.summary()[:100])
        return res

    async def _check(self, code: str, context: str = "") -> VerifyResult:
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
        infos = [m.get("data", "") for m in msgs if m.get("severity") == "info"]
        sorry_items = resp.get("sorries", []) or []
        goals = [s.get("goal", "") for s in sorry_items if s.get("goal")]
        # The REPL lists `sorry` syntax it elaborated; a sorryAx produced any other way
        # (a tactic, a metaprogram) only shows up as Lean's warning, so count both.
        sorry_warnings = sum(1 for w in warnings if "sorry" in w)
        return VerifyResult(ok=not errors, errors=errors,
                            sorries=max(len(sorry_items), sorry_warnings),
                            warnings=warnings, goals=goals, infos=infos)

    async def axiom_audit(self, code: str, name: str) -> AuditResult:
        """`#print axioms` answers with an info message. Anything other than an explicit
        list of standard axioms (or "does not depend on any axioms") fails the audit."""
        res = await self.check(code + f"\n#print axioms {name}")
        if res.errors:
            return AuditResult(ok=False, note="; ".join(res.errors[:2]))
        report = "\n".join(res.infos + res.warnings)
        m = AXIOM_LINE.search(report)
        if m:
            axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
            bad = [a for a in axioms if a not in STANDARD_AXIOMS]
            return AuditResult(ok=not bad, axioms=axioms,
                               note="" if not bad else f"non-standard axioms: {bad}")
        if f"'{name}' does not depend on any axioms" in report:
            return AuditResult(ok=True, axioms=[])
        return AuditResult(ok=False, note=f"no axiom report from Lean for {name}; failing closed")

    async def close(self) -> None:
        await self._restart()


def make_verifier(cfg) -> LeanVerifier:
    if cfg.lean_mode == "file":
        return FileLeanVerifier(cfg.lean_project_dir, cfg.lean_timeout_s, cfg.max_heartbeats)
    if cfg.lean_mode == "repl":
        if not cfg.lean_repl_bin:
            raise RuntimeError("LEAN_MODE=repl requires LEAN_REPL_BIN")
        return ReplLeanVerifier(cfg.lean_project_dir, cfg.lean_repl_bin,
                                cfg.lean_timeout_s, cfg.max_heartbeats,
                                startup_timeout_s=cfg.lean_startup_timeout_s)
    if cfg.lean_mode == "fake":
        from ..testing import default_fake_lean
        return default_fake_lean()
    # Never fall back to the simulator: it accepts any proof of a theorem it has no rule for.
    raise ValueError(f"unknown LEAN_MODE {cfg.lean_mode!r} (expected fake, file or repl)")
