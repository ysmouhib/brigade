# Open Research & Formalization Roadmap

`HJBrigade` provides an axiom-clean, zero-Mathlib Lean 4 foundation spanning Hales–Jewett, Multidimensional HJ, Van der Waerden, Schur, Graph & Multicolor Ramsey Theory, Density Hales–Jewett, and Moser numbers.

## Completed Milestones
1. **Unconditional Hales–Jewett, Multidimensional HJ & Van der Waerden** (`hales_jewett_shelah`, `multidimensional_hales_jewett`, `van_der_waerden`).
2. **Graph & Multicolor Ramsey Theory** (`graph_ramsey`, `erdos_szekeres`, Greenwood–Gleason `erdos_szekeres_even`, `multicolor_triangle_ramsey`, plus exact `ramsey_3_3_exact`, `ramsey_3_4_exact`, `ramsey_3_5_exact`, `ramsey_4_4_exact`, `ramsey_3_3_3_exact`).
3. **Schur's Theorem & Exact Schur Numbers** (`multicolor_ramsey_implies_schur`, unconditional `schur_theorem`, and exact `schur_1_exact`, `schur_2_exact`, `schur_3_exact`).
4. **Parameterizable Hypergraph Reflection & Van der Waerden Bounds** (`HyperCert`, `checkHyperCertSym_sound`, `checkVdWCertSym_sound`, `vdw_3_2_exact`, `vdw_4_2_exact` with $W(4,2)=35$, and `vdw_3_3_gt_26`).
5. **Exact Binary Density `DHJ(2)`** (`sperner_dhj_two`, `dhj_two_exact`: $c_{d, 2} = \binom{d}{\lfloor d/2 \rfloor}$ via Greene–Kleitman symmetric chain decomposition).
6. **Closed Polymath-1 Ternary Values $c_{1,3} .. c_{4,3}$ & Moser Numbers $c'_{1,3} .. c'_{4,3}$**:
   - `c_1_3_exact` ($2$), `c_2_3_exact` ($6$), `c_3_3_exact` ($18$) + `c_3_3_unique_18` + `c_4_3_exact` ($52$), plus `c_5_3_ge_150` ($\le 156$) and `c_6_3_ge_450` ($\le 468$).
   - `moser_1_3_exact` ($2$), `moser_2_3_exact` ($6$), `moser_3_3_exact` ($16$), `moser_3_3_strict_gap` ($16 < 18$), and $43 \le c'_{4,3} \le 48$.
7. **Finite HJ Bounds**: `hj_two_exact`, `hj_3_2_exact`, `hj_4_2_gt_4`, `hj_3_3_gt_4`.

---

## Next Open Formalization Targets

### 1. Van der Waerden $W(3, 3) = 27$ & Schur $S(4) = 45$
- **Current status**: `vdw_3_3_gt_26` ($W(3, 3) > 26$) and `schur_3_exact` ($S(3) = 14$) are kernel-verified in `ExactBounds.lean`.
- **Next step**: Partition $W(3,3) \le 27$ and $S(4) \le 45$ into modular sub-certificates (sharding top-level `HyperCert` branches into separate Lean definitions so elaboration stays shallow) and combine with a 44-element sum-free 4-coloring witness for $S(4) > 44$.

### 2. Two-Color Graph Ramsey $R(4, 5) = 25$ & $R(3, 6) = 18$
- **Current status**: $R(3,3)=6$, $R(3,4)=9$, $R(3,5)=14$, $R(4,4)=18$, $R(3,3,3)=17$ are closed.
- **Next step**: Add vertex-removal / McKay-Radziszowski degree-regularity lemmas to prove $R(3, 6) = 18$ (paired with the 17-vertex witness) and $R(4, 5) = 25$.

### 3. Closing Moser $c'_{4, 3} \le 43$ via Exact Orbital LP / Farkas Certificate
- **Current status**: `43 ≤ c'_{4,3} ≤ 48` (`moser_4_3_ge_43`, `moser_4_3_upper_48`).
- **Next step**: Formalize `checkFarkasMoser_sound` proving $\sum_w c_w \mathbf{1}_A(w) \le M$ from dual line weights $y_L \ge 0$ + one-point branching.

### 4. Narrowing $150 \le c_{5, 3} \le 156$ and Upper Bounds for `HJ(3, 3)`, `HJ(4, 2)`
- **Current status**: `c_5_3_ge_150` / `c_5_3_upper` ($156$), `hj_3_3_gt_4`, `hj_4_2_gt_4`.
- **Next step**: Classify 52-point and 51-point line-free slices of $[3]^4$ for `c_5_3_exact`, and add $S_d$-coordinate symmetry breaking to `CertTree` / `HyperCert`.

### 5. Full Asymptotic Density Hales–Jewett (`DHJ(3)` / `DHJ(k)`)
- **Current status**: `dhj_two_exact` (arbitrary $d$) and `dhj_implies_hj`.
- **Next step**: Formalize equal-slices / mean-square density increment for **`DHJ(3)`** and Roth's theorem ($r_3(N) = o(N)$).
