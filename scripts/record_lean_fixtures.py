#!/usr/bin/env python3
"""Record real Lean outputs as contract-test fixtures. Run once after scripts/setup_lean.sh
(and again after every Lean upgrade), from the repository root:

    python3 scripts/record_lean_fixtures.py

It writes server/tests/fixtures/lean/<case>.cli.txt and .cli.rc from `lake env lean`, and
<case>.repl.json from the Lean REPL when it is built. server/tests/test_lean_fixtures.py
replays them, so a change in how Lean or the REPL reports errors, sorries or axioms makes
the tests fail instead of silently weakening verification. Commit the files it writes.
"""
from __future__ import annotations
import json
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "server" / "tests" / "fixtures" / "lean"
HEADER = "import Mathlib\nset_option maxHeartbeats 400000\n\n"

# Each case declares a theorem named `t` and prints its axioms.
CASES = {
    "sorry": "theorem t : (1 : ℕ) = 1 := by\n  sorry\n#print axioms t",
    "standard_axioms": "theorem t (p : Prop) : p ∨ ¬p := Classical.em p\n#print axioms t",
    "no_axioms": "theorem t : True := trivial\n#print axioms t",
    "custom_axiom": "axiom cheat : False\ntheorem t : (1 : ℕ) = 2 := cheat.elim\n#print axioms t",
    "error": "theorem t : (1 : ℕ) = 2 := by\n  norm_num\n#print axioms t",
}


def _path(env: str, default: pathlib.Path) -> pathlib.Path:
    value = os.getenv(env)
    if not value:
        return default
    p = pathlib.Path(value)
    return p if p.is_absolute() else (ROOT / p).resolve()


PROJ = _path("LEAN_PROJECT_DIR", ROOT / "lean" / "BrigadeLean")
REPL = _path("LEAN_REPL_BIN", ROOT / "lean" / "repl" / ".lake" / "build" / "bin" / "repl")


def record_cli() -> None:
    scratch = PROJ / ".brigade_scratch"
    scratch.mkdir(exist_ok=True)
    for name, code in CASES.items():
        f = scratch / "Check.lean"
        f.write_text(HEADER + code + "\n", encoding="utf-8")
        print(f"-- lake env lean: {name} (imports Mathlib, may take a minute)")
        try:
            p = subprocess.run(["lake", "env", "lean", str(f)], cwd=PROJ, capture_output=True,
                               text=True, encoding="utf-8", timeout=900)
        finally:
            f.unlink(missing_ok=True)
        out = (p.stdout + p.stderr).replace(str(f), "Check.lean")   # keep local paths out
        (OUT / f"{name}.cli.txt").write_text(out, encoding="utf-8")
        (OUT / f"{name}.cli.rc").write_text(f"{p.returncode}\n", encoding="utf-8")


def record_repl() -> None:
    if not REPL.exists():
        print(f"-- REPL not built at {REPL}; skipping REPL fixtures")
        return
    cmds = [{"cmd": HEADER.strip()}] + [{"cmd": code, "env": 0} for code in CASES.values()]
    stdin = "\n\n".join(json.dumps(c) for c in cmds) + "\n\n"
    print("-- Lean REPL: all cases in one session")
    p = subprocess.run(["lake", "env", str(REPL)], cwd=PROJ, input=stdin, capture_output=True,
                       text=True, encoding="utf-8", timeout=1800)
    replies, text, dec = [], p.stdout, json.JSONDecoder()
    i = 0
    while i < len(text):
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text):
            break
        obj, i = dec.raw_decode(text, i)
        replies.append(obj)
    if len(replies) != len(cmds):
        sys.exit(f"expected {len(cmds)} REPL replies, got {len(replies)}:\n{text[:2000]}\n{p.stderr[:2000]}")
    for name, reply in zip(CASES, replies[1:]):
        (OUT / f"{name}.repl.json").write_text(json.dumps(reply, indent=1, ensure_ascii=False) + "\n",
                                                encoding="utf-8")


def main() -> int:
    import shutil
    if not shutil.which("lake"):
        sys.exit("'lake' is not on PATH. Run:  source ~/.elan/env   (or open a new terminal)")
    if not (PROJ / "lakefile.lean").exists() and not (PROJ / "lakefile.toml").exists():
        sys.exit(f"no Lean project at {PROJ}; run scripts/setup_lean.sh first")
    OUT.mkdir(parents=True, exist_ok=True)
    toolchain = (PROJ / "lean-toolchain").read_text(encoding="utf-8").strip()
    (OUT / "TOOLCHAIN").write_text(toolchain + "\n", encoding="utf-8")
    record_cli()
    record_repl()
    print(f"== wrote fixtures for {toolchain} to {OUT.relative_to(ROOT)}; now run the tests")
    return 0


if __name__ == "__main__":
    sys.exit(main())
