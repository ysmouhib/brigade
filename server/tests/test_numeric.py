"""Unit tests for the Skeptic's sympy-backed numeric falsifier."""
import pytest

from app.numeric import ProbeError, find_counterexample, probe


def test_true_identity_has_no_counterexample():
    cands = [{"n": k} for k in range(0, 30)]
    assert find_counterexample("Eq(Mod({n}**2 + {n}, 2), 0)", cands) is None


def test_false_claim_is_caught():
    # "every prime is odd" fails at n = 2
    expr = "Or(Not(isprime({n})), Eq(Mod({n}, 2), 1))"
    cands = [{"n": k} for k in range(1, 10)]
    assert find_counterexample(expr, cands) == {"n": 2}


def test_probe_evaluates_single_assignment():
    assert probe("Gt({a} + {b}, {a})", {"a": 3, "b": 1}) is True
    assert probe("Gt({a} + {b}, {a})", {"a": 3, "b": 0}) is False


@pytest.mark.parametrize("bad", [
    "__import__('os').system('id')",
    "({n}).__class__",
    "open('/etc/passwd')",          # unknown name -> rejected by whitelist
])
def test_sanitizer_blocks_injection(bad):
    with pytest.raises(ProbeError):
        probe(bad, {"n": 1})
