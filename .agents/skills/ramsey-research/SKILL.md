---
name: ramsey-research
description: Daily workflow for conducting Ramsey Theory, Hales-Jewett, Van der Waerden, Schur, DHJ, and Graph Ramsey formalization research in brigade + HJBrigade using Lean 4, MCP tools, blueprint inspection, and DISCOVERIES.md.
---

# Daily Ramsey Theory Research Workflow (`brigade`)

Use this skill whenever exploring finite bounds, proving new Lean 4 Ramsey theorems, or tracking discoveries in `HJBrigade`.

## 1. Ground First in Compiled Theorems (`index`)
Never reinvent definitions or guess declaration names:
- MCP tool: `brigade_search_premises` with keywords like `"GraphRamseyUpper"`, `"HasMonoSchur"`, `"HasMonoAP"`, `"HyperCert"`, `"IsGeomLineFree"`, `"shelahHJDim"`.
- CLI equivalent:
  ```bash
  python scripts/run_cli.py index --query "<keyword>"
  ```

## 2. Check the Research Frontier (`lab` & `explore`)
Before launching a search or proof attempt:
- Read recent discoveries and open problems via `brigade_lab_note` (`action="list"`) or inspect `research/DISCOVERIES.md`.
- Sweep small cases cleanly to spot structural patterns (palindromes, circulants, Paley residues, cosets, Fujimura simplices):
  - MCP tool: `brigade_explore` (`family="hj"|"vdw"|"schur"|"ramsey"|"dhj"|"moser"`)
  - CLI: `python scripts/run_cli.py explore schur --r 3 --start 10 --stop 14 --json`

## 3. Draft & Iterate with `blueprint`
For non-trivial Lean 4 theorems:
1. Write a clean draft `.lean` file with structured helper lemmas and `sorry` placeholders.
2. Call `brigade_blueprint` (or `python scripts/run_cli.py blueprint path/to/Draft.lean`).
3. Use the exact elaborated `⊢` goal states and retrieved `HJBrigade` premise hints to close one `sorry` at a time.
4. Before spending effort proving a finite bound `P(N)`, check it combinatorially with `brigade_certify` so false sub-lemmas are killed immediately.

## 4. Non-Negotiable Soundness Gates (`I1`–`I4`)
Every Lean theorem committed to `HJBrigade` must satisfy:
- **Zero** `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `partial`, or `@[implemented_by`.
- Only kernel-checked `decide` and standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Verify incrementally with `brigade_verify_snippet`, build with `python scripts/build_lean.py` (uses `lake build` or `lean.exe` fallback), run `python scripts/run_cli.py audit-repo`, and log verified results via `brigade_lab_note` (`action="add"`).
