"""Unit tests for the verification layer itself (lint, parsing, fake semantics)."""
from app.lean.verifier import (AXIOM_LINE, ERROR_LINE, FakeLean, lint_proof,
                               parse_lean_output, split_theorem_blocks)


def test_lint_catches_every_forbidden_token():
    for bad in ["sorry", "admit", "axiom cheat : False", "native_decide",
                "exact sorryAx _", "unsafe def x", "@[implemented_by y]"]:
        assert lint_proof(f"intro h\n{bad}\n"), bad
    assert lint_proof("intro h\nexact h") == []
    # substrings of honest identifiers must not fire ('axiom ' has a trailing space)
    assert lint_proof("exact axioms_of_choice_free h") == []


def test_split_theorem_blocks():
    code = ("theorem a : True := by\n  trivial\n\n"
            "theorem b (n : \u2115) : n = n := by\n  rfl\n")
    blocks = dict(split_theorem_blocks(code))
    assert set(blocks) == {"a", "b"}
    assert "trivial" in blocks["a"] and "rfl" in blocks["b"]
    assert "rfl" not in blocks["a"]


def test_lean_output_parsing_regexes():
    out = ("Check_x.lean:4:2: error: unknown identifier 'Evenn'\n"
           "Check_x.lean:9:0: warning: declaration uses 'sorry'\n")
    assert ERROR_LINE.findall(out) == ["unknown identifier 'Evenn'"]
    m = AXIOM_LINE.search("'thm' depends on axioms: [propext, Classical.choice, Quot.sound]")
    assert m and "Classical.choice" in m.group(1)


def test_file_mode_keeps_info_messages_in_either_format():
    """`trace` and `#print` output reach infos whether or not Lean prefixes 'info:'."""
    out = ("/s/Check_x.lean:5:4: info: brigade-cascade: lemma_1 ring\n"
           "/s/Check_x.lean:7:0: brigade-cascade: lemma_2 simp\n"
           "/s/Check_x.lean:9:0: warning: declaration uses 'sorry'\n"
           "/s/Check_x.lean:11:2: error: unsolved goals\n"
           "n : ℕ\n")
    res = parse_lean_output(1, out)
    assert res.infos == ["brigade-cascade: lemma_1 ring", "brigade-cascade: lemma_2 simp"]
    assert res.sorries == 1 and res.errors == ["unsolved goals"]


async def test_fakelean_semantics():
    fake = FakeLean(rules={"t": (["magic"], "error: unsolved goals")},
                    bad_tokens={"BAD": "error: unknown identifier 'BAD'"})
    ok = await fake.check("theorem t : True := by\n  magic")
    assert ok.ok and ok.sorries == 0
    miss = await fake.check("theorem t : True := by\n  trivial")
    assert not miss.ok and "unsolved" in miss.errors[0]
    gate = await fake.check("theorem t : True := by\n  sorry")
    assert gate.ok and gate.sorries == 1  # statement gate: no errors, one sorry
    bad = await fake.check("theorem t : BAD := by\n  sorry")
    assert not bad.ok
    audit = await fake.axiom_audit("theorem t : True := by\n  magic", "t")
    assert audit.ok and "sorryAx" not in audit.axioms
    dirty = await fake.axiom_audit("... sorry ...", "t")
    assert not dirty.ok
