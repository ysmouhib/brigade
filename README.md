# `brigade` (`HJBrigade`) — Antigravity Ramsey Theory & Lean 4 Research Workbench

[![CI](https://github.com/ysmouhib/brigade/actions/workflows/ci.yml/badge.svg)](https://github.com/ysmouhib/brigade/actions/workflows/ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-blue.svg)](lean-toolchain)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

`brigade` is an Antigravity-native, self-contained **Lean 4.35.0** formalization library (`HJBrigade`), combinatorial certificate compiler, parameter-sweep explorer, and neuro-symbolic proving workbench for **Ramsey Theory** — spanning **Hales–Jewett**, **Multidimensional Hales–Jewett**, **Van der Waerden**, **Schur's Theorem**, **Graph & Multicolor Ramsey Numbers**, **Density Hales–Jewett (`DHJ`)**, and **Moser Numbers** over $[3]^d$.

It features **173 kernel-verified Lean 4 theorems across 19 modules** (zero Mathlib dependency, zero `sorry`, zero `native_decide`), a parameterizable DPLL reflection checker (`HyperCert`), an interactive discovery log (`research/DISCOVERIES.md`), Antigravity workspace skills (`.agents/skills/`), and a zero-dependency **stdio MCP server** (`python -m brigade mcp`).

---

## Formalized Results (Machine-Checked in Lean 4.35.0, Zero `sorry`)

Every exported theorem passes static linting (`I4`) and `#print axioms` (`I2`), depending exclusively on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound` — or axiom-free).

| Theorem / Module | Formal Statement / Result | Proof Method |
| --- | --- | --- |
| `hales_jewett_shelah`, `hales_jewett` ([Shelah.lean](HJBrigade/Theorems/Shelah.lean)) | `∀ k r ≥ 1, HJUpper (shelahHJDim k r) k r` | Shelah's 1988 Cube / Equal-Ends induction (`shelah_equal_ends`) |
| `multidimensional_hales_jewett` ([MultidimensionalHJ.lean](HJBrigade/Theorems/MultidimensionalHJ.lean)) | `∀ m k r ≥ 1, ∃ D ≥ 1, MHJUpper m D k r` | Product subspace induction (`mhj_shelah`) via `encodeMap` |
| `van_der_waerden` ([Shelah.lean](HJBrigade/Theorems/Shelah.lean)) | `∀ k r ≥ 1, ∃ N ≥ 1, HasMonoAP N k r` | Coordinate-sum projection `hj_implies_vdw` ([VanDerWaerden.lean](HJBrigade/Reductions/VanDerWaerden.lean)) |
| `erdos_szekeres`, `graph_ramsey`, `erdos_szekeres_even` ([GraphRamsey/Basic.lean](HJBrigade/GraphRamsey/Basic.lean)) | `GraphRamseyUpper (erdosSzekeresBound s t) s t` + Greenwood–Gleason parity tightening | Pivot neighbor induction + `handshaking_even` (`% 2`) |
| `multicolor_triangle_ramsey` ([GraphRamsey/Basic.lean](HJBrigade/GraphRamsey/Basic.lean)) | `∀ r ≥ 1, ∃ N ≥ 1, MulticolorRamseyUpper N r 3` | Pigeonhole star + color drop `ramsey_triangle_step` |
| `ramsey_3_3_exact` .. `ramsey_4_4_exact`, `ramsey_3_3_3_exact` ([ExactRamsey.lean](HJBrigade/GraphRamsey/ExactRamsey.lean)) | $R(3,3)=6,\; R(3,4)=9,\; R(3,5)=14,\; R(4,4)=18,\; R(3,3,3)=17$ | Greenwood–Gleason + $C_5$, $\mathbb{Z}_8$, $\mathbb{Z}_{13}$, Paley $P_{17}$, $\mathrm{GF}(16)$ witnesses |
| `schur_theorem`, `schur_1_exact`, `schur_2_exact`, `schur_3_exact` ([Schur.lean](HJBrigade/Reductions/Schur.lean), [ExactBounds.lean](HJBrigade/Theorems/ExactBounds.lean)) | $\forall r \ge 1,\; \exists n \ge 1, \text{HasMonoSchur}\; n\; r$; exact $S(1)=2,\; S(2)=5,\; S(3)=14$ | Difference coloring reduction (`multicolor_ramsey_implies_schur`) + `HyperCert` |
| `vdw_3_2_exact`, `vdw_4_2_exact`, `vdw_3_3_gt_26` ([ExactBounds.lean](HJBrigade/Theorems/ExactBounds.lean)) | $W(3,2)=9,\; W(4,2)=35,\; W(3,3)>26$ | 1,423-node `HyperCert` (`checkVdWCertSym_sound`) + AP-free colorings |
| `hj_two_exact`, `hj_3_2_exact`, `hj_4_2_gt_4`, `hj_3_3_gt_4` ([BaseAndAlphabetTwo.lean](HJBrigade/Theorems/BaseAndAlphabetTwo.lean), [ExactBounds.lean](HJBrigade/Theorems/ExactBounds.lean)) | $HJ(2,r)=r$, $HJ(3,2)=4$, $HJ(4,2)>4$, $HJ(3,3)>4$ | Pigeonhole on step words + 441-node `CertTree` (`checkCertSym_sound`) |
| `dhj_two_exact` / `sperner_dhj_two` ([Sperner.lean](HJBrigade/Density/Sperner.lean)) | $c_{d, 2} = \binom{d}{\lfloor d/2 \rfloor}$ for all $d$ | Constructive Greene–Kleitman Symmetric Chain Decomposition |
| `c_1_3_exact` .. `c_4_3_exact`, `c_3_3_unique_18`, `c_5_3_ge_150`, `c_6_3_ge_450` ([ExactDHJ.lean](HJBrigade/Density/ExactDHJ.lean), [Fujimura.lean](HJBrigade/Density/Fujimura.lean)) | $c_{1,3}=2,\; c_{2,3}=6,\; c_{3,3}=18,\; c_{4,3}=52,\; 150\le c_{5,3}\le 156,\; 450\le c_{6,3}\le 468$ | 9-bit slice uniqueness (`Slice9.lean`) + Fujimura $S_d$-simplex reduction |
| `moser_1_3_exact` .. `moser_3_3_exact`, `moser_3_3_strict_gap`, `moser_4_3_ge_43` ([Moser.lean](HJBrigade/Density/Moser.lean)) | $c'_{1,3}=2,\; c'_{2,3}=6,\; c'_{3,3}=16 < 18 = c_{3,3},\; 43 \le c'_{4,3} \le 48$ | 2D edge-midpoint forcing + geometric Fujimura reduction |
| `checkHyperCertSym_sound`, `checkCertSym_sound`, `checkNoClique_sound` ([HypergraphCert.lean](HJBrigade/Certificates/HypergraphCert.lean), [CertTree.lean](HJBrigade/Certificates/CertTree.lean), [GraphRamsey/Basic.lean](HJBrigade/GraphRamsey/Basic.lean)) | Parameterized reflection checkers for arbitrary hypergraphs & clique avoidance | Structural tree induction + color-symmetry involution (`swapColor0`) |

---

## Using `brigade` Daily with Antigravity

### 1. Register as an Antigravity MCP Server
Point Antigravity's MCP configuration at `brigade` (template in [mcp_config.example.json](mcp_config.example.json)):

```json
{
  "mcpServers": {
    "brigade": {
      "command": "python",
      "args": ["-m", "brigade", "--project-dir", "C:/Users/youne/.gemini/antigravity/scratch/hj-brigade", "mcp"]
    }
  }
}
```

Exposed MCP tools:
- `brigade_search_premises` — search all 173 compiled `HJBrigade` theorems & definitions
- `brigade_blueprint` — extract elaborated `⊢` goal states for every `sorry`, matching lemmas, and axioms
- `brigade_verify_snippet` — run `I4` lint + real Lean 4 compile + `#print axioms`
- `brigade_certify` — solve & emit kernel-checked witnesses/trees for `hj`, `vdw`, `schur`, `ramsey`, `dhj`, `moser`
- `brigade_explore` — sweep Ramsey parameter ranges and inspect witness symmetry/periodicity
- `brigade_audit_repo` — audit the repository's theorems and axiom compliance
- `brigade_lab_note` — read and append entries to [research/DISCOVERIES.md](research/DISCOVERIES.md)

Workspace skills under [.agents/skills/](.agents/skills/ramsey-research/SKILL.md) guide Antigravity automatically through daily proof exploration and certificate compression.

### 2. Build, Audit & Test Everything

```bash
python scripts/build_lean.py       # Uses `lake build`, with incremental `lean.exe` fallback
python scripts/run_cli.py audit-repo
python scripts/run_cli.py bench    # 22-problem Ramsey/HJ/VdW/Schur/DHJ/Moser benchmark suite
python -m pytest -v
```

### 3. CLI Quick Reference

```bash
# Search compiled lemmas & inspect interactive draft files
python scripts/run_cli.py index --query "GraphRamseyUpper"
python scripts/run_cli.py blueprint path/to/Draft.lean

# Sweep parameter frontiers & track discoveries
python scripts/run_cli.py explore vdw --k 3 --r 2 --start 7 --stop 10 --json
python scripts/run_cli.py lab list

# Certify & verify finite bounds directly in Lean 4
python scripts/run_cli.py certify-hj --d 4 --k 3 --r 2 --verify
python scripts/run_cli.py certify-vdw --n 35 --k 4 --r 2 --verify
python scripts/run_cli.py certify-schur --n 14 --r 3 --verify
python scripts/run_cli.py certify-ramsey --n 17 --s 4 --t 4 --verify
python scripts/run_cli.py certify-dhj --d 5 --k 3 --verify
python scripts/run_cli.py certify-moser --d 4 --verify

# Automated invariant-enforcing orchestrator (0-LLM fastpath + LLM repair loop)
python scripts/run_cli.py prove "Prove GraphRamseyUpper 9 3 4"
```

---

## Architecture & Repository Layout

- `HJBrigade/Core/`: `FinQuant.lean`, `FinEncode.lean`, `Line.lean`
- `HJBrigade/Theorems/`: `BaseAndAlphabetTwo.lean`, `ColorFocusing.lean`, `Shelah.lean`, `MultidimensionalHJ.lean`, `ExactBounds.lean`
- `HJBrigade/GraphRamsey/`: `Basic.lean`, `ExactRamsey.lean`
- `HJBrigade/Reductions/`: `VanDerWaerden.lean`, `Schur.lean`
- `HJBrigade/Density/`: `Sperner.lean`, `Slice9.lean`, `Fujimura.lean`, `ExactDHJ.lean`, `Moser.lean`
- `HJBrigade/Certificates/`: `CertTree.lean`, `HypergraphCert.lean`
- `brigade/`: `lean_verifier.py`, `skeptic_hj.py`, `hypergraph.py`, `density_hj.py`, `explorer.py`, `blueprint.py`, `library_index.py`, `mcp_server.py`, `orchestrator.py`, `bench.py`, `cli.py`, `llm.py`, `agents.py`, `prompts.py`, `models.py`
- `.agents/skills/`: `ramsey-research/SKILL.md`, `hypergraph-certificates/SKILL.md`
- `research/`: `DISCOVERIES.md`, `notes.jsonl`
- `benchmarks/`: `hj_suite.jsonl` (22-problem benchmark suite)
- `docs/`: [MATHLIB_BRIDGE.md](docs/MATHLIB_BRIDGE.md), [RESEARCH_ROADMAP.md](docs/RESEARCH_ROADMAP.md)
- `scripts/`: `run_cli.py`, `build_lean.py`, `generate_exact_bounds.py`, `generate_density_bounds.py`, `enable_mathlib.ps1`
- `tests/`: Real-Lean integration tests across invariants, certificates, Graph Ramsey, Schur, VdW, explorer, MCP server, blueprint, orchestrator, and CLI.

---

## Soundness Invariants (`I1`–`I4`)

1. **I1 (Verifier Gate)**: A proof node enters `VERIFIED` *only* after `RealLeanVerifier.check()` succeeds with `ok=True` and `sorries=0` on code containing its pinned statement.
2. **I2 (Whole-File Re-Check & Axiom Audit)**: Acceptance requires full compilation plus `#print axioms` confirming all dependencies lie inside `{propext, Classical.choice, Quot.sound}`.
3. **I3 (Statement Pinning)**: Statements lock after `trace_state; sorry` elaboration in `check_statement`; provers can only emit tactic bodies after `:= by`.
4. **I4 (Static Linter)**: Proof bodies are rejected pre-Lean if they contain `sorry`, `admit`, `axiom`, `native_decide`, `sorryAx`, `unsafe`, `opaque`, `partial`, `@[implemented_by`, `Lean.ofReduceBool`, or `Lean.trustCompiler` (ignoring `--` and nested `/- ... -/` comments).

## Further Research & Citation

See [docs/RESEARCH_ROADMAP.md](docs/RESEARCH_ROADMAP.md) and [research/DISCOVERIES.md](research/DISCOVERIES.md) for current open frontiers ($W(3,3)\le 27$, $S(4)\le 45$, $R(4,5)=25$, $c'_{4,3}=43$, $c_{5,3}=150$, $HJ(3,3)$ and $HJ(4,2)$ upper bounds, asymptotic `DHJ(3)`). Citation metadata is provided in [CITATION.cff](CITATION.cff).
