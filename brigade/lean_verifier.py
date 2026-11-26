"""Real Lean 4 verifier backend with strict soundness invariants I1, I2, I4."""

from __future__ import annotations

import asyncio
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import uuid

from .models import AuditResult, VerifyResult

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Forbidden constructs inside proof bodies (I4). Kernel-checked `decide` is explicitly permitted.
FORBIDDEN_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"\baxiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("opaque", re.compile(r"\bopaque\b")),
    ("partial", re.compile(r"\bpartial\b")),
    ("@[implemented_by", re.compile(r"@\[implemented_by\b")),
    ("Lean.ofReduceBool", re.compile(r"\bLean\.ofReduceBool\b")),
    ("Lean.trustCompiler", re.compile(r"\bLean\.trustCompiler\b")),
]

_ERROR_RE = re.compile(r"^[^:\n]+(?::[^:\n]+)*:(\d+):(\d+):\s*error:\s*(.*)$")
_WARN_RE = re.compile(r"^[^:\n]+(?::[^:\n]+)*:(\d+):(\d+):\s*warning:\s*(.*)$")
_INFO_RE = re.compile(r"^[^:\n]+(?::[^:\n]+)*:(\d+):(\d+):\s*info:\s*(.*)$")
_AXIOMS_RE = re.compile(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]")
_NO_AXIOMS_RE = re.compile(r"'([^']+)'\s+does not depend on any axioms")
_SORRY_GOAL_RE = re.compile(r"declaration uses [`']sorry[`']")


def _strip_lean_comments(text: str) -> str:
    """Strip `--` line comments and nested `/- ... -/` block comments/docstrings."""
    out: list[str] = []
    n = len(text)
    i = 0
    block_depth = 0
    in_line = False
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
        elif in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(nxt)
                i += 2
            elif ch == '"':
                in_string = False
                i += 1
            else:
                i += 1
        else:
            if ch == '"':
                in_string = True
                out.append(ch)
                i += 1
            elif ch == "-" and nxt == "-":
                in_line = True
                out.append("  ")
                i += 2
            elif ch == "/" and nxt == "-":
                block_depth = 1
                out.append("  ")
                i += 2
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def lint_proof(body: str) -> list[str]:
    """Enforce Invariant I4: forbid cheat tokens and non-kernel shortcuts in proof bodies."""
    cleaned = _strip_lean_comments(body)
    hits: list[str] = []
    for label, pat in FORBIDDEN_PATTERNS:
        if pat.search(cleaned):
            hits.append(f"forbidden token in proof: '{label}'")
    return hits


def _safe_exists(path: Path) -> bool:
    try:
        return path.exists()
    except OSError:
        return False


def find_elan_toolchain_bin() -> Path | None:
    """Locate Lean 4 toolchain binaries (`lake` / `lean`), favoring PATH then `.elan`."""
    exe_ext = ".exe" if os.name == "nt" else ""
    for env_key in ("BRIGADE_LEAN_BIN", "LEAN_BIN_DIR"):
        val = os.environ.get(env_key)
        if val and _safe_exists(Path(val) / f"lean{exe_ext}"):
            return Path(val)

    which_lake = shutil.which("lake")
    if which_lake:
        return Path(which_lake).parent

    home_elan = Path.home() / ".elan" / "toolchains"
    if _safe_exists(home_elan):
        preferred = home_elan / "leanprover--lean4---v4.35.0" / "bin"
        if _safe_exists(preferred):
            return preferred
        try:
            for child in sorted(home_elan.iterdir(), reverse=True):
                candidate = child / "bin"
                if _safe_exists(candidate / f"lean{exe_ext}"):
                    return candidate
        except OSError:
            pass

    elan_bin = Path.home() / ".elan" / "bin"
    if _safe_exists(elan_bin / f"lake{exe_ext}"):
        return elan_bin
    return None


def parse_lean_output(stdout: str, stderr: str) -> tuple[list[str], list[str], int, list[str]]:
    """Parse Lean compiler diagnostics into errors, warnings, sorry count, and goal snippets."""
    combined = "\n".join(part for part in (stdout, stderr) if part).splitlines()
    errors: list[str] = []
    warnings: list[str] = []
    goals: list[str] = []
    sorries = 0

    current_bucket: list[str] | None = None
    in_goal = False
    goal_lines: list[str] = []

    def flush_goal() -> None:
        nonlocal in_goal, goal_lines
        if goal_lines:
            goals.append("\n".join(goal_lines).strip())
            goal_lines = []
        in_goal = False

    for line in combined:
        m_err = _ERROR_RE.match(line)
        m_warn = _WARN_RE.match(line)
        if m_err:
            flush_goal()
            msg = f"L{m_err.group(1)}:{m_err.group(2)}: {m_err.group(3)}"
            errors.append(msg)
            current_bucket = errors
            if "unsolved goals" in m_err.group(3):
                in_goal = True
        elif m_warn:
            flush_goal()
            msg = f"L{m_warn.group(1)}:{m_warn.group(2)}: {m_warn.group(3)}"
            warnings.append(msg)
            current_bucket = warnings
            if _SORRY_GOAL_RE.search(m_warn.group(3)):
                sorries += 1
        elif (m_info := _INFO_RE.match(line)):
            flush_goal()
            current_bucket = None
            first = m_info.group(3).strip()
            if first or "⊢" in line:
                in_goal = True
                if first:
                    goal_lines.append(first)
        elif line.startswith((" ", "\t", "⊢")):
            if current_bucket is not None:
                current_bucket[-1] = current_bucket[-1] + "\n" + line
            if in_goal or line.lstrip().startswith("⊢"):
                in_goal = True
                goal_lines.append(line)
        else:
            flush_goal()
            current_bucket = None

    flush_goal()
    return errors, warnings, sorries, goals


class RealLeanVerifier:
    """Real Lean 4 verifier running inside a Lake project with precompiled `.olean`s."""

    def __init__(
        self,
        project_dir: Path | str,
        timeout_s: float = 60.0,
        max_heartbeats: int = 400_000,
    ):
        self.project_dir = Path(project_dir).resolve()
        self.timeout_s = timeout_s
        self.max_heartbeats = max_heartbeats
        self.bin_dir = find_elan_toolchain_bin()
        if self.bin_dir is None:
            raise RuntimeError(
                "Could not locate Lean/Lake binaries. Ensure `lake` is on PATH or elan is installed."
            )
        exe_ext = ".exe" if os.name == "nt" else ""
        self.lake_bin = self.bin_dir / f"lake{exe_ext}"
        self.lean_bin = self.bin_dir / f"lean{exe_ext}"
        self._lean_path_cache: str | None = None
        self._scratch_dir = self.project_dir / ".brigade_scratch"
        self._scratch_dir.mkdir(parents=True, exist_ok=True)

    def _resolve_lean_path(self) -> str:
        if self._lean_path_cache is not None:
            return self._lean_path_cache
        if self.lake_bin.exists():
            proc = subprocess.run(
                [str(self.lake_bin), "env", "printenv", "LEAN_PATH"],
                cwd=str(self.project_dir),
                capture_output=True,
                text=True,
                timeout=30,
            )
            if proc.returncode == 0 and proc.stdout.strip():
                self._lean_path_cache = proc.stdout.strip()
                return self._lean_path_cache
        self._lean_path_cache = str(self.project_dir / ".lake" / "build" / "lib" / "lean")
        return self._lean_path_cache

    def _run_lean_file_sync(self, code: str) -> tuple[int, str, str, float]:
        tmp_path = self._scratch_dir / f"check_{uuid.uuid4().hex[:10]}.lean"
        tmp_path.write_text(code, encoding="utf-8")
        t0 = time.perf_counter()
        try:
            env = os.environ.copy()
            env["LEAN_PATH"] = self._resolve_lean_path()
            cmd = [str(self.lean_bin), str(tmp_path)] if self.lean_bin.exists() else [
                str(self.lake_bin), "env", "lean", str(tmp_path)
            ]
            proc = subprocess.run(
                cmd,
                cwd=str(self.project_dir),
                env=env,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=self.timeout_s,
            )
            elapsed = time.perf_counter() - t0
            return proc.returncode, proc.stdout, proc.stderr, elapsed
        except subprocess.TimeoutExpired:
            elapsed = time.perf_counter() - t0
            return 124, "", f"check.lean:1:1: error: Lean timed out after {self.timeout_s}s", elapsed
        finally:
            try:
                tmp_path.unlink(missing_ok=True)
            except OSError:
                pass

    def build_check_source(
        self,
        code: str,
        context: str = "",
        imports: list[str] | None = None,
        namespace: str | None = None,
    ) -> str:
        imp_list = imports if imports is not None else ["HJBrigade"]
        header_lines = [f"import {m}" for m in imp_list]
        header_lines.append(f"set_option maxHeartbeats {self.max_heartbeats}")
        if namespace:
            header_lines.append(f"open {namespace}")
        parts = ["\n".join(header_lines)]
        if context.strip():
            parts.append(context.strip())
        if code.strip():
            parts.append(code.strip())
        return "\n\n".join(parts) + "\n"

    async def check(
        self,
        code: str,
        context: str = "",
        imports: list[str] | None = None,
        namespace: str | None = "HJBrigade",
    ) -> VerifyResult:
        full_src = self.build_check_source(code, context=context, imports=imports, namespace=namespace)
        rc, stdout, stderr, elapsed = await asyncio.to_thread(self._run_lean_file_sync, full_src)
        errors, warnings, sorries, goals = parse_lean_output(stdout, stderr)
        if rc != 0 and not errors:
            errors = [f"Lean exited with status {rc}: {(stderr or stdout).strip()[:400]}"]
        return VerifyResult(
            ok=(rc == 0 and not errors),
            errors=errors,
            warnings=warnings,
            sorries=sorries,
            goals=goals,
            raw_output="\n".join(p for p in (stdout, stderr) if p),
            elapsed_s=elapsed,
        )

    async def check_statement(
        self,
        theorem_header: str,
        context: str = "",
        imports: list[str] | None = None,
        namespace: str | None = "HJBrigade",
    ) -> VerifyResult:
        """Elaborate a statement header with `trace_state; sorry` to capture the exact Lean goal."""
        stmt_code = f"{theorem_header.strip()} := by\n  trace_state\n  sorry"
        return await self.check(stmt_code, context=context, imports=imports, namespace=namespace)

    async def axiom_audit(
        self,
        code: str,
        theorem_name: str,
        imports: list[str] | None = None,
        namespace: str | None = "HJBrigade",
    ) -> AuditResult:
        """Compile `code` with `#print axioms <theorem_name>` and enforce Invariant I2."""
        lint_hits = lint_proof(code)
        if lint_hits:
            return AuditResult(
                ok=False,
                theorem_name=theorem_name,
                note="; ".join(lint_hits),
            )
        audit_code = f"{code.rstrip()}\n\n#print axioms {theorem_name}\n"
        res = await self.check(audit_code, imports=imports, namespace=namespace)
        if not res.ok or res.sorries > 0:
            return AuditResult(
                ok=False,
                theorem_name=theorem_name,
                note="; ".join(res.errors[:2]) or f"{res.sorries} sorry(ies) present",
            )
        raw = res.raw_output
        if _NO_AXIOMS_RE.search(raw):
            return AuditResult(ok=True, theorem_name=theorem_name, axioms=[], note="axiom-free")
        m = _AXIOMS_RE.search(raw)
        if not m:
            return AuditResult(
                ok=False,
                theorem_name=theorem_name,
                note=f"Could not parse `#print axioms {theorem_name}` from Lean output",
            )
        axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
        bad = [a for a in axioms if a not in STANDARD_AXIOMS]
        return AuditResult(
            ok=(not bad),
            theorem_name=theorem_name,
            axioms=axioms,
            note="" if not bad else f"forbidden non-standard axioms: {bad}",
        )

    async def audit_existing_module(
        self, module_name: str, theorem_names: list[str], namespace: str | None = "HJBrigade"
    ) -> list[AuditResult]:
        """Audit theorems already compiled in `module_name` via `#print axioms`."""
        if not theorem_names:
            return []
        lines = [f"#print axioms {name}" for name in theorem_names]
        res = await self.check("\n".join(lines), imports=[module_name], namespace=namespace)
        results: list[AuditResult] = []
        raw = res.raw_output
        for name in theorem_names:
            if not res.ok:
                results.append(AuditResult(ok=False, theorem_name=name, note="; ".join(res.errors[:2])))
                continue
            pat_none = re.compile(rf"'(?:[^']*\.)?{re.escape(name)}'\s+does not depend on any axioms")
            pat_ax = re.compile(rf"'(?:[^']*\.)?{re.escape(name)}'\s+depends on axioms:\s*\[([^\]]*)\]")
            if pat_none.search(raw):
                results.append(AuditResult(ok=True, theorem_name=name, axioms=[], note="axiom-free"))
            elif (m := pat_ax.search(raw)):
                axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
                bad = [a for a in axioms if a not in STANDARD_AXIOMS]
                results.append(
                    AuditResult(
                        ok=(not bad),
                        theorem_name=name,
                        axioms=axioms,
                        note="" if not bad else f"forbidden axioms: {bad}",
                    )
                )
            else:
                results.append(
                    AuditResult(
                        ok=False,
                        theorem_name=name,
                        note=f"No `#print axioms` output found for `{name}`",
                    )
                )
        return results

    async def close(self) -> None:
        return None
