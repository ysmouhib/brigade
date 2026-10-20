"""Replay real Lean and REPL outputs recorded by scripts/record_lean_fixtures.py.

Skipped until the fixtures exist (they need a machine with Lean + Mathlib). Once recorded
and committed, these pin how Brigade reads errors, sorries and `#print axioms`, for the
exact toolchain in fixtures/lean/TOOLCHAIN. Re-record after every Lean upgrade.
"""
from __future__ import annotations
import json
from pathlib import Path

import pytest

from app.lean.verifier import STANDARD_AXIOMS, parse_axiom_report, parse_lean_output
from tests.test_repl_contract import FixtureRepl

FIX = Path(__file__).parent / "fixtures" / "lean"
CODE = "theorem t : True := trivial"   # the replies are fixed; the code is not re-checked


def _cli(name: str):
    path = FIX / f"{name}.cli.txt"
    if not path.exists():
        pytest.skip("no recorded `lake env lean` output: run scripts/record_lean_fixtures.py")
    rc = int((FIX / f"{name}.cli.rc").read_text(encoding="utf-8").strip())
    return rc, path.read_text(encoding="utf-8")


def _repl(name: str) -> FixtureRepl:
    path = FIX / f"{name}.repl.json"
    if not path.exists():
        pytest.skip("no recorded REPL output: build the REPL and run scripts/record_lean_fixtures.py")
    return FixtureRepl(json.loads(path.read_text(encoding="utf-8")))


def test_cli_sorry_is_never_accepted():
    rc, out = _cli("sorry")
    assert parse_lean_output(rc, out).sorries >= 1
    audit = parse_axiom_report(rc, out, "t")
    assert not audit.ok and "sorryAx" in audit.axioms


def test_cli_standard_axioms_pass():
    rc, out = _cli("standard_axioms")
    res, audit = parse_lean_output(rc, out), parse_axiom_report(rc, out, "t")
    assert res.ok and res.sorries == 0
    assert audit.ok and set(audit.axioms) <= STANDARD_AXIOMS and audit.axioms


def test_cli_no_axioms_pass():
    rc, out = _cli("no_axioms")
    assert parse_lean_output(rc, out).ok and parse_axiom_report(rc, out, "t").ok


def test_cli_custom_axiom_fails():
    rc, out = _cli("custom_axiom")
    audit = parse_axiom_report(rc, out, "t")
    assert not audit.ok and "cheat" in audit.axioms


def test_cli_error_is_not_ok():
    rc, out = _cli("error")
    res = parse_lean_output(rc, out)
    assert not res.ok and res.errors
    assert not parse_axiom_report(rc, out, "t").ok


async def test_repl_sorry_is_never_accepted():
    v = _repl("sorry")
    assert (await v.check(CODE)).sorries >= 1
    assert not (await v.axiom_audit(CODE, "t")).ok


async def test_repl_standard_axioms_pass():
    v = _repl("standard_axioms")
    res, audit = await v.check(CODE), await v.axiom_audit(CODE, "t")
    assert res.ok and res.sorries == 0
    assert audit.ok and set(audit.axioms) <= STANDARD_AXIOMS and audit.axioms


async def test_repl_no_axioms_pass():
    assert (await _repl("no_axioms").axiom_audit(CODE, "t")).ok


async def test_repl_custom_axiom_fails():
    audit = await _repl("custom_axiom").axiom_audit(CODE, "t")
    assert not audit.ok and "cheat" in audit.axioms


async def test_repl_error_is_not_ok():
    v = _repl("error")
    assert not (await v.check(CODE)).ok
    assert not (await v.axiom_audit(CODE, "t")).ok
