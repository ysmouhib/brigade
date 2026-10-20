"""Contract tests: ReplLeanVerifier against the Lean REPL's real JSON output format.

RECORDED_SORRY_DECL is copied from leanprover-community/repl's own test suite at tag
v4.15.0 (test/have_by_sorry.expected.out, second command). The `#print axioms` replies
use the REPL's severity mapping from REPL/JSON.lean at the same tag: Lean's
`information` messages arrive as "severity": "info". Brigade's audit used to read only
warnings and errors, so it never saw the axiom list and accepted every proof.
"""
from __future__ import annotations

from app.lean.verifier import STANDARD_AXIOMS, ReplLeanVerifier

RECORDED_SORRY_DECL = {
    "sorries": [{"proofState": 1, "pos": {"line": 1, "column": 36},
                 "goal": "x : Int\n⊢ x = x", "endPos": {"line": 1, "column": 41}}],
    "messages": [{"severity": "warning", "pos": {"line": 1, "column": 8},
                  "endPos": {"line": 1, "column": 11}, "data": "declaration uses 'sorry'"}],
    "env": 1}


def _info(text: str) -> dict:
    return {"severity": "info", "pos": {"line": 9, "column": 0},
            "endPos": {"line": 9, "column": 13}, "data": text}


def _axioms_reply(name: str, axioms: list[str]) -> dict:
    return {"messages": [_info(f"'{name}' depends on axioms: [{', '.join(axioms)}]")], "env": 2}


class FixtureRepl(ReplLeanVerifier):
    """Answers every command with a fixed REPL reply; no Lean process is started."""

    def __init__(self, reply: dict):
        super().__init__(project_dir=".", repl_bin="repl")
        self._base_env, self.reply, self.sent = 0, reply, []

    async def _ensure_started(self):
        class _Alive:
            returncode = None
        self._proc = _Alive()

    async def _roundtrip(self, obj, timeout):
        self.sent.append(obj)
        return self.reply


FINAL = "theorem thm_main : 2 + 2 = 4 := by\n  norm_num"


async def test_recorded_sorry_declaration_is_never_acceptable():
    res = await FixtureRepl(RECORDED_SORRY_DECL).check("theorem foo (x : Int) : x = x := by sorry")
    assert res.sorries >= 1 and res.goals == ["x : Int\n⊢ x = x"]


async def test_sorry_warning_counts_even_without_sorry_entries():
    """A sorryAx inserted by a tactic or metaprogram leaves no `sorry` syntax for the
    REPL to list, but Lean still warns that the declaration uses sorry."""
    reply = {"messages": [RECORDED_SORRY_DECL["messages"][0]], "sorries": [], "env": 1}
    res = await FixtureRepl(reply).check(FINAL)
    assert res.sorries >= 1


async def test_axiom_audit_reads_the_info_message():
    audit = await FixtureRepl(_axioms_reply("thm_main", sorted(STANDARD_AXIOMS))).axiom_audit(
        FINAL, "thm_main")
    assert audit.ok and audit.axioms == sorted(STANDARD_AXIOMS)


async def test_axiom_audit_rejects_sorry_and_custom_axioms():
    for axioms in (["propext", "sorryAx"], ["Classical.choice", "my_cheat_axiom"]):
        audit = await FixtureRepl(_axioms_reply("thm_main", axioms)).axiom_audit(FINAL, "thm_main")
        assert not audit.ok, axioms
        assert any(a not in STANDARD_AXIOMS for a in audit.axioms)


async def test_axiom_audit_accepts_a_proof_with_no_axioms():
    reply = {"messages": [_info("'thm_main' does not depend on any axioms")], "env": 2}
    assert (await FixtureRepl(reply).axiom_audit(FINAL, "thm_main")).ok


async def test_axiom_audit_fails_closed_when_lean_reports_nothing():
    audit = await FixtureRepl({"messages": [], "env": 2}).axiom_audit(FINAL, "thm_main")
    assert not audit.ok and "no axiom report" in audit.note
