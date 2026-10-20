"""Cheap numeric falsification with sympy, used by the Skeptic before any Lean effort is spent.

The Skeptic agent proposes a boolean sympy expression *template* (with `{var}` placeholders)
plus candidate assignments. We substitute, parse with a whitelisted sympy namespace, and
evaluate. `False` at any candidate is a counterexample certificate; `True` everywhere is
merely "not falsified" (never a proof).
"""
from __future__ import annotations
import asyncio
import multiprocessing as mp
import re
import threading
import sympy
from sympy import (Eq, Ne, Lt, Le, Gt, Ge, Mod, And, Or, Not, Abs, gcd, lcm,
                   factorial, floor, ceiling, sqrt, Rational, Integer, binomial)
from sympy.ntheory import isprime

SAFE = {
    "Eq": Eq, "Ne": Ne, "Lt": Lt, "Le": Le, "Gt": Gt, "Ge": Ge, "Mod": Mod,
    "And": And, "Or": Or, "Not": Not, "Abs": Abs, "gcd": gcd, "lcm": lcm,
    "factorial": factorial, "floor": floor, "ceiling": ceiling, "sqrt": sqrt,
    "Rational": Rational, "Integer": Integer, "binomial": binomial, "isprime": isprime,
}

_ALLOWED = re.compile(r"^[\w\s+\-*/%(),=<>!&|.]{1,500}$")

# Candidates are LLM-proposed. Counterexamples worth finding this way are small; a huge
# value (factorial of 10**100) would never finish, so it is skipped as inconclusive.
MAX_CANDIDATE_ABS = 10 ** 6
# Wall-clock limit for one batch of probes in the worker process.
PROBE_TIMEOUT_S = 10.0


class ProbeError(Exception):
    pass


def _sanitize(expr: str) -> None:
    if "__" in expr or not _ALLOWED.match(expr):
        raise ProbeError(f"expression rejected by sanitizer: {expr!r}")
    # dots only allowed in decimal literals, never attribute access
    for m in re.finditer(r"\.", expr):
        i = m.start()
        before = expr[i - 1] if i > 0 else ""
        after = expr[i + 1] if i + 1 < len(expr) else ""
        if not (before.isdigit() or after.isdigit()):
            raise ProbeError("attribute access is not allowed in probe expressions")


def probe(template: str, assignment: dict[str, int]) -> bool:
    """Return the truth value of `template` at `assignment`. Raises ProbeError if inconclusive."""
    try:
        expr = template.format(**{k: f"({int(v)})" for k, v in assignment.items()})
    except (KeyError, ValueError, IndexError) as e:
        raise ProbeError(f"bad template/assignment: {e}")
    _sanitize(expr)
    try:
        val = sympy.sympify(expr, locals=dict(SAFE))
    except Exception as e:  # noqa: BLE001 - sympy raises many types
        raise ProbeError(f"sympy could not parse: {e}")
    if val in (sympy.true, True):
        return True
    if val in (sympy.false, False):
        return False
    raise ProbeError(f"expression did not evaluate to a boolean: {val!r}")


def find_counterexample(template: str, candidates: list[dict[str, int]]) -> dict[str, int] | None:
    """Return the first candidate that makes the claim false, or None. Inconclusive probes
    (unparseable, non-boolean, or a value beyond MAX_CANDIDATE_ABS) are skipped.

    Synchronous and unbounded in time: the server calls find_counterexample_async."""
    for cand in candidates[:64]:
        try:
            if any(abs(int(v)) > MAX_CANDIDATE_ABS for v in cand.values()):
                continue
            if probe(template, cand) is False:
                return {k: int(v) for k, v in cand.items()}
        except (ProbeError, TypeError, ValueError):
            continue
    return None


def _worker_main(conn) -> None:
    """Runs in the probe process: answer (template, candidates) requests until closed."""
    while True:
        try:
            template, candidates = conn.recv()
        except (EOFError, OSError):
            return
        try:
            conn.send(("ok", find_counterexample(template, candidates)))
        except Exception as e:  # noqa: BLE001 - report, keep serving
            conn.send(("err", f"{type(e).__name__}: {e}"))


class _ProbeWorker:
    """One long-lived process for numeric probes, killed and replaced on timeout.

    A thread cannot be stopped mid-computation, so runaway sympy work is isolated in a
    process. Starting it once (not per probe) keeps the sympy import cost off each call,
    which matters on Windows, where processes are spawned rather than forked."""

    def __init__(self):
        self._proc = None
        self._conn = None
        self._lock = threading.Lock()

    def _start(self) -> None:
        # "spawn" everywhere: forking a multi-threaded server process can deadlock the
        # child, and it is what Windows does anyway, so both platforms behave the same.
        ctx = mp.get_context("spawn")
        parent, child = ctx.Pipe()
        proc = ctx.Process(target=_worker_main, args=(child,), daemon=True,
                           name="brigade-numeric-probe")
        proc.start()
        child.close()
        self._proc, self._conn = proc, parent

    def _kill(self) -> None:
        proc, self._proc, self._conn = self._proc, None, None
        if proc is not None:
            proc.kill()
            proc.join(timeout=2)

    def run(self, template: str, candidates: list[dict[str, int]], timeout_s: float):
        with self._lock:
            if self._proc is None or not self._proc.is_alive():
                self._start()
            try:
                self._conn.send((template, list(candidates)))
                if not self._conn.poll(timeout_s):
                    self._kill()
                    raise ProbeError(f"numeric probe timed out after {timeout_s:g}s")
                kind, value = self._conn.recv()
            except (EOFError, OSError, BrokenPipeError) as e:
                self._kill()
                raise ProbeError(f"numeric probe worker failed: {e}") from None
            if kind == "err":
                raise ProbeError(value)
            return value


_WORKER = _ProbeWorker()


async def find_counterexample_async(template: str, candidates: list[dict[str, int]],
                                    timeout_s: float = PROBE_TIMEOUT_S) -> dict[str, int] | None:
    """find_counterexample in an isolated worker process, awaited without blocking the
    event loop. Raises ProbeError if the batch exceeds timeout_s (the worker is replaced)."""
    return await asyncio.to_thread(_WORKER.run, template, candidates, timeout_s)
