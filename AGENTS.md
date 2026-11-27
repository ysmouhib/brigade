# Agent Guide for `brigade` (`HJBrigade`)

When developing or proving new Ramsey Theory theorems in this repository with Antigravity (via MCP tools / `.agents/skills/`) or automated pipelines, follow this workflow:

## 1. Core Library Modules (`HJBrigade` — 19 Modules, 173 Theorems)
Before creating new definitions, query what is already compiled (or use the `brigade_search_premises` MCP tool):
```bash
python scripts/run_cli.py index --query "<keyword>"
```
Key canonical declarations (`import HJBrigade` + `open HJBrigade`):
- **Hales–Jewett & Multidimensional HJ**: `Word d k`, `Line d k`, `HJUpper d k r`, `HJUpper.mono_dim`, `HJUpper.mono_colors`, `hj_two_exact`, `CombSubspace.pullback_hj`, `color_focused_dichotomy`, `shelahHJDim`, `hales_jewett_shelah`, `hales_jewett`, `MHJUpper`, `mhj_shelah`, `multidimensional_hales_jewett`
- **Van der Waerden & Schur**: `HasMonoAP`, `HasMonoAPFor`, `hasMonoAP_iff_for`, `hj_implies_vdw`, `van_der_waerden`, `vdw_3_2_exact`, `vdw_4_2_exact`, `vdw_3_3_gt_26`, `HasMonoSchur`, `HasMonoSchurFor`, `multicolor_ramsey_implies_schur`, `schur_theorem`, `schur_1_exact`, `schur_2_exact`, `schur_3_exact`
- **Graph & Multicolor Ramsey**: `GraphRamseyUpper`, `MulticolorRamseyUpper`, `erdos_szekeres_step`, `erdos_szekeres`, `graph_ramsey`, `handshaking_even`, `erdos_szekeres_even` (Greenwood–Gleason), `ramsey_triangle_step`, `multicolor_triangle_ramsey`, `ramsey_3_3_exact`, `ramsey_3_4_exact`, `ramsey_3_5_exact`, `ramsey_4_4_exact`, `ramsey_3_3_3_exact`, `checkNoClique_sound`, `checkNoMonoClique_sound`
- **Density Hales–Jewett & Moser**: `wordCard`, `IsLineFree`, `lineFree_slice_bound`, `dhj_implies_hj`, `sperner_dhj_two`, `dhj_two_exact`, `c_1_3_exact`..`c_4_3_exact`, `c_3_3_unique_18`, `c_5_3_ge_150`, `c_6_3_ge_450`, `GeomLine`, `IsGeomLineFree`, `moser_1_3_exact`..`moser_3_3_exact`, `moser_3_3_strict_gap`, `moser_4_3_upper_48`, `moser_4_3_ge_43`
- **General Hypergraph Reflection Certificates**: `CertTree`, `checkCertSym_sound`, `HyperCert`, `checkHyperCert_sound`, `checkHyperCertSym_sound`, `checkVdWCertSym_sound`, `checkSchurCertSym_sound`

## 2. Antigravity MCP Server & Workspace Skills
- `.agents/skills/ramsey-research/SKILL.md`: daily Ramsey exploration -> certification -> `blueprint` -> `audit-repo` -> `DISCOVERIES.md` workflow.
- `.agents/skills/hypergraph-certificates/SKILL.md`: choosing and optimizing `HyperCert`, `CertTree`, and clique witnesses.
- Start stdio MCP server for Antigravity (`mcp_config.example.json`):
  ```bash
  python -m brigade --project-dir . mcp
  ```

## 3. Interactive Blueprint, Sweep & Lab Loop
1. Sweep finite frontiers and log discoveries:
   ```bash
   python scripts/run_cli.py explore schur --r 3 --start 10 --stop 14 --json
   python scripts/run_cli.py lab list
   ```
2. Draft a Lean file with `sorry` subgoals and inspect via `blueprint`:
   ```bash
   python scripts/run_cli.py blueprint path/to/Draft.lean
   ```
3. Compile kernel-checked finite bounds before attempting general proofs:
   ```bash
   python scripts/run_cli.py certify-hj --d 4 --k 3 --r 2 --verify
   python scripts/run_cli.py certify-vdw --n 35 --k 4 --r 2 --verify
   python scripts/run_cli.py certify-schur --n 14 --r 3 --verify
   python scripts/run_cli.py certify-ramsey --n 17 --s 4 --t 4 --verify
   ```

## 4. Non-Negotiable Soundness Rules (`I1`–`I4`)
- **Zero `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `partial`, or `native_decide`** in committed Lean files.
- **Only kernel-checked `decide`** and standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) are permitted.
- Build (`lake build` or `python scripts/build_lean.py`) and run `python scripts/run_cli.py audit-repo` before committing.
