# `hj-brigade` — Lean 4 Formalization & Neuro-Symbolic Proving Toolkit for Hales–Jewett and Ramsey Theory

[![CI](https://github.com/ysmouhib/hj-brigade/actions/workflows/ci.yml/badge.svg)](https://github.com/ysmouhib/hj-brigade/actions/workflows/ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-blue.svg)](lean-toolchain)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

`hj-brigade` is a self-contained, zero-`sorry`, zero-`native_decide` **Lean 4.35.0** formalization library and combinatorial certificate toolkit focused on **Ramsey Theory**, the **Hales–Jewett theorem**, **Multidimensional Hales–Jewett**, **Van der Waerden's theorem**, and **Density Hales–Jewett (`DHJ`)**.

It replaces the non-functional mock architecture of [`ysmouhib/brigade`](https://github.com/ysmouhib/brigade) (`FakeLean` + empty `lean/` directory) with real kernel-verified Lean proofs, fast DPLL/density certificate compilers, and agent-native tooling (`blueprint`, `index`, `audit-repo`, `bench`).

---

## Formalized Results (Machine-Checked in Lean 4.35.0, Zero `sorry`)

Every exported theorem passes static linting (`I4`) and `#print axioms` (`I2`), depending exclusively on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound` — or axiom-free).

| Theorem / Module | Formal Statement / Result | Proof Method |
| --- | --- | --- |
| `hales_jewett_shelah` ([Shelah.lean](HJBrigade/Theorems/Shelah.lean)) | `∀ k r ≥ 1, HJUpper (shelahHJDim k r) k r` | Shelah's 1988 primitive-recursive Cube / Equal-Ends proof (`shelah_equal_ends`) |
| `hales_jewett` ([Shelah.lean](HJBrigade/Theorems/Shelah.lean)) | `∀ k r ≥ 1, ∃ d ≥ 1, HJUpper d k r` | Direct existential corollary of `hales_jewett_shelah` |
| `multidimensional_hales_jewett` ([MultidimensionalHJ.lean](HJBrigade/Theorems/MultidimensionalHJ.lean)) | `∀ m k r ≥ 1, ∃ D ≥ 1, MHJUpper m D k r` | Product subspace induction (`mhj_shelah`) via `encodeMap` profiles |
| `van_der_waerden` ([Shelah.lean](HJBrigade/Theorems/Shelah.lean)) | `∀ k r ≥ 1, ∃ N ≥ 1, HasMonoAP N k r` | Coordinate-sum projection `hj_implies_vdw` ([VanDerWaerden.lean](HJBrigade/Reductions/VanDerWaerden.lean)) |
| `hj_two_exact` ([BaseAndAlphabetTwo.lean](HJBrigade/Theorems/BaseAndAlphabetTwo.lean)) | `∀ r ≥ 1, HJUpper r 2 r ∧ ¬ HJUpper (r - 1) 2 r` | `fin_pigeonhole` on step words + Hamming-weight coloring |
| `color_focused_dichotomy` ([ColorFocusing.lean](HJBrigade/Theorems/ColorFocusing.lean)) | Dichotomy for `r` color-focused lines + `CombSubspace.pullback_hj` | Constructive finite surjectivity (`fin_inj_surj`) |
| `dhj_two_exact` / `sperner_dhj_two` ([Sperner.lean](HJBrigade/Density/Sperner.lean)) | `c_{d, 2} = natChoose d (d / 2)` for all `d` | Constructive Greene–Kleitman Symmetric Chain Decomposition (`symChains`) |
| `dhj_implies_hj` ([Sperner.lean](HJBrigade/Density/Sperner.lean)) | `(∀ A, IsLineFree A → wordCard A ≤ M) → r * M < k^d → HJUpper d k r` | Color-class cardinality partition (`wordCard_sum_colors`) |
| `c_1_3_exact`, `c_2_3_exact`, `c_3_3_exact`, `c_4_3_ge_52` ([ExactDHJ.lean](HJBrigade/Density/ExactDHJ.lean)) | $c_{1,3}=2,\; c_{2,3}=6,\; c_{3,3}=18,\; c_{4,3} \ge 52$ | `lineFree_slice_bound` + kernel-checked extremal witnesses |
| `hj_3_2_exact`, `vdw_3_2_exact` ([ExactBounds.lean](HJBrigade/Theorems/ExactBounds.lean)) | `HJ(3, 2) = 4` (`¬ HJUpper 3 3 2 ∧ HJUpper 4 3 2`) & `W(3, 2) = 9` | 441-node `CertTree` verified via `checkCertSym2_sound` + `hj_implies_vdw` |
| `checkCert_sound`, `checkCertSym_sound` ([CertTree.lean](HJBrigade/Certificates/CertTree.lean)) | General `r`-color symmetry-broken DPLL reflection checker | `swapColor0` permutation involution + structural tree soundness |

---

## How to Use `hj-brigade` for Research

### 1. Build & Audit Everything (< 10 seconds, zero Mathlib download required)

```bash
lake build
python scripts/run_cli.py audit-repo
python scripts/run_cli.py bench
python -m pytest -v
```

### 2. Interactive Agent Workflow (`blueprint` + `index`)
When collaborating with an interactive AI coding agent (Antigravity, Claude Code, Codex, Cursor) on new Lean proofs (see [AGENTS.md](AGENTS.md)):

```bash
# Search compiled HJBrigade lemmas before formalizing
python scripts/run_cli.py index --query "ColorFocused"

# Inspect a draft Lean file: extract exact `⊢` goals for every `sorry`, retrieve premises, audit completed theorems
python scripts/run_cli.py blueprint path/to/Draft.lean
```

### 3. Combinatorial Certificate Compilers (`certify-hj` / `certify-dhj`)
Find and compile kernel-checked Lean 4 witnesses or reflection trees (`CertTree`) for finite Hales–Jewett and Density Hales–Jewett bounds:

```bash
# Exact coloring upper/lower bounds (e.g., HJ(3,2) at d=4 or HJ(2,3) at d=3)
python scripts/run_cli.py certify-hj --d 4 --k 3 --r 2 --verify
python scripts/run_cli.py certify-hj --d 3 --k 2 --r 3 --verify

# Line-free extremal density lower bounds in [k]^d
python scripts/run_cli.py certify-dhj --d 4 --k 3 --verify
```

### 4. Automated Multi-Agent Prover (`prove`)
Run the invariant-enforcing orchestrator (`I1`–`I4`: statement pinning, static lint, per-lemma Skeptic refutation, tactic cascades, batched sibling checks, persistent `ProofLedger`, and `#print axioms` audit):

```bash
python scripts/run_cli.py prove "Prove HJUpper (shelahHJDim 3 2) 3 2"
```

Set `GEMINI_API_KEY`, `OPENAI_API_KEY`, or `ANTHROPIC_API_KEY` (and optionally `PROVER_BASE_URL` / `PROVER_MODEL`) to enable multi-agent LLM brainstorming and repair loops for custom lemmas.

---

## Architecture & Repository Layout

- `HJBrigade/Core/`: `FinQuant.lean`, `FinEncode.lean`, `Line.lean`
- `HJBrigade/Theorems/`: `BaseAndAlphabetTwo.lean`, `ColorFocusing.lean`, `Shelah.lean`, `MultidimensionalHJ.lean`, `ExactBounds.lean`
- `HJBrigade/Reductions/`: `VanDerWaerden.lean`
- `HJBrigade/Density/`: `Sperner.lean`, `ExactDHJ.lean`
- `HJBrigade/Certificates/`: `CertTree.lean`
- `brigade/`: `lean_verifier.py`, `skeptic_hj.py`, `density_hj.py`, `blueprint.py`, `library_index.py`, `orchestrator.py`, `bench.py`, `cli.py`, `llm.py`, `agents.py`, `prompts.py`, `models.py`
- `benchmarks/`: `hj_suite.jsonl` (12-problem verification/refutation benchmark suite)
- `docs/`: [MATHLIB_BRIDGE.md](docs/MATHLIB_BRIDGE.md), [RESEARCH_ROADMAP.md](docs/RESEARCH_ROADMAP.md)
- `scripts/`: `run_cli.py`, `generate_exact_bounds.py`, `generate_density_bounds.py`, `enable_mathlib.ps1`
- `tests/`: Real-Lean 4 integration tests across invariants, certificates, density/MHJ, blueprint, orchestrator, and CLI.

---

## Soundness Invariants (`I1`–`I4`)

1. **I1 (Verifier Gate)**: A proof node enters `VERIFIED` *only* after `RealLeanVerifier.check()` succeeds with `ok=True` and `sorries=0` on code containing its pinned statement.
2. **I2 (Whole-File Re-Check & Axiom Audit)**: Acceptance requires whole-file compilation plus `#print axioms` confirming all dependencies lie inside `{propext, Classical.choice, Quot.sound}`.
3. **I3 (Statement Pinning)**: Statements lock after `trace_state; sorry` elaboration in `check_statement`; provers can only emit tactic bodies after `:= by`.
4. **I4 (Static Linter)**: Proof bodies are rejected pre-Lean if they contain `sorry`, `admit`, `axiom`, `native_decide`, `sorryAx`, `unsafe`, `opaque`, `partial`, `@[implemented_by`, `Lean.ofReduceBool`, or `Lean.trustCompiler` (ignoring `--` and nested `/- ... -/` comments).

## Further Research & Citation

See [docs/RESEARCH_ROADMAP.md](docs/RESEARCH_ROADMAP.md) for open problems (closing $c_{4,3} \le 52$ via Farkas duality, Moser numbers, asymptotic `DHJ(3)`, and `HJ(3,3)` certificates). Citation metadata is provided in [CITATION.cff](CITATION.cff).
