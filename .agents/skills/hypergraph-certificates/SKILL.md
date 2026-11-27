---
name: hypergraph-certificates
description: Workflow for producing kernel-checked Lean 4 upper and lower bound certificates across Hales-Jewett, Van der Waerden, Schur, DHJ, Moser, and Graph Ramsey using HyperCert, CertTree, and checkNoClique_sound.
---

# Hypergraph Certificate Engineering (`brigade`)

Use this skill when certifying finite Ramsey-type upper or lower bounds cleanly in Lean 4 without `native_decide`.

## 1. Choosing the Right Certificate Checker
| Problem Family | Lower Bound (Counterexample) | Upper Bound (Refutation Tree) | Lean Bridge Theorem |
| --- | --- | --- | --- |
| Van der Waerden (`HasMonoAP N k r`) | `HasMonoAPFor N k r w` + `decide` | `HyperCert (Nat × Nat) r` + centered root `N / 2` | `checkVdWCertSym_sound` |
| Schur (`HasMonoSchur n r`) | `HasMonoSchurFor n r w` + `decide` | `HyperCert (Nat × Nat × Nat) r` | `checkSchurCertSym_sound` |
| Hales–Jewett (`HJUpper d k r`) | `HasMonoLineFor d k r c` + `decide` | `CertTree r` (`swapColor0` sym) | `checkCertSym_sound` |
| 2-Color Graph Ramsey (`GraphRamseyUpper N s t`) | Circulant / Paley / edge-SAT `Fin N → Fin N → Bool` | `erdos_szekeres_step` / `erdos_szekeres_even` | `checkNoClique_sound` |
| Multicolor Graph Ramsey (`MulticolorRamseyUpper N r k`) | Algebraic coset (`GF(q)`) / table `Fin N → Fin N → Fin r` | `ramsey_triangle_step` | `checkNoMonoClique_sound` |
| DHJ / Moser (`IsLineFree` / `IsGeomLineFree`) | Fujimura / local-search subset | `third_slice_le_9` / slice induction | `lineFree_slice_bound` |

## 2. Keeping Kernel `decide` Trees Fast
- Break symmetry on `rootV` centered near `N // 2` (`W(4,2) = 35` drops to ~1,423 nodes with `root = 17` and unit forcing + backjumping).
- For `HyperCert` witness edges with repeated vertices (like Schur `(x, x, z)`), deduplicate vertices during DPLL propagation while keeping the full `(x, y, z)` tuple as the Lean witness.
- Avoid generating single AST literals exceeding ~4,000 nodes (or increase modularity by splitting at the root child level so Lean elaborates shallow definitions without hitting `maxRecDepth`).
- Always confirm compiled certificates via `python scripts/run_cli.py certify-<family> ... --verify` or `brigade_certify` with `verify=True`.
