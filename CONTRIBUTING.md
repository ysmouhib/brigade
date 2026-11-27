# Contributing to `brigade` (`HJBrigade`)

Thank you for helping grow `brigade` into a rigorous open-source Lean 4 research library for Ramsey Theory.

## Soundness Rules (Non-Negotiable)

All committed Lean 4 theorems under `HJBrigade/` must satisfy Invariants `I1`–`I4`:

1. **Zero cheat tokens (`I4`)**: no `sorry`, `admit`, `axiom`, `native_decide`, `sorryAx`, `unsafe`, `opaque`, `partial`, `@[implemented_by ...]`, `@[extern ...]`, `@[csimp ...]`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.
2. **Standard axioms only (`I2`)**: every exported theorem and lemma must depend solely on `{propext, Classical.choice, Quot.sound}` (or be axiom-free), verified via `#print axioms`.
3. **Kernel-checked finite bounds**: use `decide` (typically via `CertTree`, `HyperCert`, `checkNoClique_sound`, or Fujimura reductions), never `native_decide`.
4. **Canonical definitions**: inspect existing declarations with `python scripts/run_cli.py index --query "<keyword>"` before introducing new types or predicates.

## Contributor Workflow

1. Draft new theorems in a `.lean` file and run `blueprint` to inspect open `sorry` goal states and matching library premises:
   ```bash
   python scripts/run_cli.py blueprint path/to/Draft.lean
   ```
2. Build all Lean modules cleanly:
   ```bash
   python scripts/build_lean.py --force
   ```
   (Uses `lake build`, with incremental `lean.exe` topological compilation fallback when needed.)
3. Run the full validation suite before opening a pull request:
   ```bash
   python scripts/run_cli.py audit-repo
   python scripts/run_cli.py bench
   python -m pytest -v
   ```
4. If you prove or falsify a new bound or discover a useful extremal pattern, record it with `python scripts/run_cli.py lab add ...` so `research/notes.jsonl` and `research/DISCOVERIES.md` stay synchronized.
