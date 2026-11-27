# Ramsey Theory Research Discoveries & Frontier Log

Tracked by `brigade lab` and `brigade_lab_note` (MCP). Every theorem marked `VERIFIED`
is compiled in Lean 4 with zero `sorry` and audited via `#print axioms`.

| # | Family | Status | Title | Theorem | Summary |
| --- | --- | --- | --- | --- | --- |
| 1 | `hj` | **VERIFIED** | Shelah Hales-Jewett & Multidimensional HJ | `hales_jewett_shelah, multidimensional_hales_jewett, van_der_waerden` | Unconditional Hales-Jewett, Multidimensional HJ, and Van der Waerden via equal-ends cube induction and encodeMap. |
| 2 | `hj` | **VERIFIED** | Exact Finite HJ(3,2) = 4 & Lower Bounds HJ(4,2) > 4, HJ(3,3) > 4 | `hj_3_2_exact, hj_4_2_gt_4, hj_3_3_gt_4` | Symmetry-broken 441-node CertTree closes HJ(3,2)=4; line-free witnesses close HJ(4,2)>4 and HJ(3,3)>4. |
| 3 | `vdw` | **VERIFIED** | Van der Waerden W(3,2)=9, W(4,2)=35 & W(3,3)>26 | `vdw_3_2_exact, vdw_4_2_exact, vdw_3_3_gt_26` | HyperCert reflection certifies Chvatal's W(4,2)=35 alongside W(3,2)=9 and a 26-element 3-AP-free 3-coloring. |
| 4 | `schur` | **VERIFIED** | Schur's Theorem & Exact Schur Numbers S(1)=2, S(2)=5, S(3)=14 | `schur_theorem, schur_1_exact, schur_2_exact, schur_3_exact` | Ramsey-to-Schur reduction proved unconditionally; S(1)=2, S(2)=5, and S(3)=14 certified via HyperCert. |
| 5 | `ramsey` | **VERIFIED** | Exact Graph & Multicolor Ramsey R(3,3)=6, R(3,4)=9, R(3,5)=14, R(4,4)=18, R(3,3,3)=17 | `ramsey_3_3_exact, ramsey_3_4_exact, ramsey_3_5_exact, ramsey_4_4_exact, ramsey_3_3_3_exact` | Erdos-Szekeres, Greenwood-Gleason parity tightening, C5, Z/8Z, Z/13Z, Paley P17, and GF(16) coset witnesses. |
| 6 | `dhj` | **VERIFIED** | Polymath-1 Ternary DHJ(3) & Moser Gaps | `dhj_two_exact, c_4_3_exact, c_5_3_ge_150, moser_3_3_strict_gap, moser_4_3_ge_43` | Exact c_{d,2}=C(d,floor(d/2)), c_{3,3}=18 (unique), c_{4,3}=52, c'_{3,3}=16 < 18, and 150 <= c_{5,3} <= 156. |
| 7 | `open` | **OPEN** | Open Frontier: W(3,3)<=27, S(4)<=45, R(4,5)=25, c_{5,3}=150, c'_{4,3}=43 | — | Next targets for orbital Farkas LP certificates and symmetry-broken HyperCert splitting. |
