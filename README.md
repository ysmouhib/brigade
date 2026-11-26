# `hj-brigade` — Neuro-Symbolic Lean 4 Prover for Ramsey Theory & Hales–Jewett

A lean-first, zero-theater successor to `ysmouhib/brigade`, engineered to produce **machine-checked Lean 4 proofs** efficiently for **Ramsey Theory** and the **Hales–Jewett theorem**.

## What Was Kept vs. Replaced from `ysmouhib/brigade`

| Component | Old `ysmouhib/brigade` | New `hj-brigade` |
| --- | --- | --- |
| **Soundness Invariants (`I1`–`I4`)** | Enforced only over `FakeLean` token mocks | Enforced against real **Lean 4.35.0** (`RealLeanVerifier`), `#print axioms`, statement pinning, and static lint |
| **Lean Library (`HJBrigade`)** | Empty `lean/.gitkeep` | Full precompiled `.olean` library culminating in **Shelah's primitive-recursive Hales–Jewett theorem** (`hales_jewett_shelah`), **`hales_jewett`**, **`van_der_waerden`**, exact **`HJ(2, r) = r`**, **`HJ(3, 2) = 4`**, and **`W(3, 2) = 9`** |
| **Skeptic & Certificate Compiler** | SymPy integer-grid evaluator | Combinatorial **DPLL + unit-propagation + backjumping solvers** (`brigade/skeptic_hj.py`) compiling SAT witnesses (`¬ HJUpper`, `¬ HasMonoAP`) and UNSAT `CertTree` proofs (`checkCertSym_sound`, `checkCertSym2_sound`) into kernel-checked Lean 4 (`by decide`, zero `native_decide`) |
| **State & Retrieval** | `_abandon_round()` wiped progress; external HTTP retrieval | Persistent JSON `ProofLedger` + local `PremiseIndex` scanning `HJBrigade/**/*.lean` + `trace_state` exact Lean goal extraction |
| **Tactic Cascade & Batching** | Stubbed | Zero-LLM `decide`/`omega`/`simp` + `HJBrigade` base/Shelah theorem cascade, batched sibling verification, and per-lemma Skeptic pre-check |

## Quickstart

### 1. Build the Lean 4 library (< 10 seconds, zero external downloads)

```powershell
lake build
```

### 2. Audit every theorem and axiom in `HJBrigade`

```powershell
python scripts/run_cli.py audit-repo
```

Every theorem across all modules passes `#print axioms` with only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound` — or axiom-free) and zero `sorryAx` or `native_decide`.

### 3. Run the Ramsey & Hales–Jewett benchmark suite

```powershell
python scripts/run_cli.py bench
```

### 4. Solve and certify finite Hales–Jewett bounds in Lean 4

```powershell
python scripts/run_cli.py certify-hj --d 3 --k 3 --r 2 --verify
python scripts/run_cli.py certify-hj --d 4 --k 3 --r 2 --verify
```

### 5. Search the `HJBrigade` theorem index & prove new claims

```powershell
python scripts/run_cli.py index --query "Shelah"
python scripts/run_cli.py prove "Prove HJUpper (shelahHJDim 3 2) 3 2"
```

Set `GEMINI_API_KEY`, `OPENAI_API_KEY`, or `ANTHROPIC_API_KEY` (and optionally `PROVER_BASE_URL` / `PROVER_MODEL`) to enable multi-agent brainstorming, formalization, and proof search for open/custom Ramsey claims.

## Soundness Invariants (`I1`–`I4`)

1. **I1 (Verifier Gate)**: A proof node enters `VERIFIED` *only* after `RealLeanVerifier.check()` returns `ok=True` and `sorries=0` on code containing the pinned theorem.
2. **I2 (Whole-File Re-Check + Axiom Audit)**: Final acceptance requires whole-file compilation plus `#print axioms <theorem>` confirming all dependencies lie inside `{propext, Classical.choice, Quot.sound}`.
3. **I3 (Statement Pinning)**: Statements lock after passing `trace_state; sorry` in `check_statement`; provers can only supply tactic bodies after `:= by`.
4. **I4 (Static Linter)**: Proof bodies are rejected prior to Lean invocation if they contain `sorry`, `admit`, `axiom`, `native_decide`, `sorryAx`, `unsafe`, `opaque`, `partial`, `@[implemented_by`, `Lean.ofReduceBool`, or `Lean.trustCompiler` (comment-aware across `--` and nested `/- ... -/`).

## Project Layout

- `HJBrigade/Core/FinQuant.lean` — Constructive finite quantification (`FinDomain`) + `fin_pigeonhole`
- `HJBrigade/Core/FinEncode.lean` — Constructive finite bijections (`FinEquiv`, `finEquivFun`, `encodeMap`)
- `HJBrigade/Core/Line.lean` — `Word`, `Line`, `IsMonoLine`, `HasMonoLine`, `HJUpper`, monotonicity lemmas
- `HJBrigade/Theorems/BaseAndAlphabetTwo.lean` — `hj_one_color`, `hj_alphabet_one`, and exact theorem `hj_two_exact : HJUpper r 2 r ∧ ¬ HJUpper (r - 1) 2 r`
- `HJBrigade/Theorems/ColorFocusing.lean` — `CombSubspace`, `pullback_hj`, `ColorFocusedLines`, `color_focused_dichotomy`
- `HJBrigade/Theorems/Shelah.lean` — `shelah_equal_ends`, `hales_jewett_shelah`, `hales_jewett`, and `van_der_waerden`
- `HJBrigade/Reductions/VanDerWaerden.lean` — `HasMonoAP`, `HasMonoAPFor`, `hj_implies_vdw`, `not_vdw_implies_not_hj`
- `HJBrigade/Certificates/CertTree.lean` — Verified reflection checkers (`checkCert_sound`, `checkCertSym2_sound`, `checkCertSym_sound`)
- `HJBrigade/Theorems/ExactBounds.lean` — Machine-checked exact finite bounds (`HJ(2,2)`, `HJ(3,2) = 4`, `W(3,2) = 9`)
- `brigade/` — Combinatorial HJ/VdW solvers, Lean verifier, premise index, persistent ledger, LLM agents, orchestrator, benchmark runner, and CLI
- `benchmarks/hj_suite.jsonl` — 8-problem Hales–Jewett & Van der Waerden verification/refutation benchmark suite
- `docs/MATHLIB_BRIDGE.md` — Mapping to `Mathlib.Combinatorics.HalesJewett` & `gdahia/ShelahHalesJewett`
