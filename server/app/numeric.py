"""Cheap numeric falsification with sympy, used by the Skeptic before any Lean effort is spent.

The Skeptic agent proposes a boolean sympy expression *template* (with `{var}` placeholders)
plus candidate assignments. We substitute, parse with a whitelisted sympy namespace, and
evaluate. `False` at any candidate is a counterexample certificate; `True` everywhere is
merely "not falsified" (never a proof).
"""
from __future__ import annotations
import re
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
    """Return the first candidate that makes the claim false, or None. Inconclusive probes are skipped."""
    for cand in candidates[:64]:
        try:
            if probe(template, cand) is False:
                return {k: int(v) for k, v in cand.items()}
        except ProbeError:
            continue
    return None
