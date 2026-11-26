# Open Research & Formalization Roadmap

`HJBrigade` provides an axiom-clean, zero-Mathlib Lean 4 foundation for Hales–Jewett, Density Hales–Jewett, and Moser number formalization.

## Completed Milestones
1. **Unconditional Hales–Jewett, Multidimensional HJ & Van der Waerden** (`hales_jewett_shelah`, `multidimensional_hales_jewett`, `van_der_waerden`).
2. **Exact Binary Density `DHJ(2)`** (`sperner_dhj_two`, `dhj_two_exact`: $c_{d, 2} = \binom{d}{\lfloor d/2 \rfloor}$ via constructive Greene–Kleitman symmetric chain decomposition).
3. **Closed Polymath-1 Ternary Values $c_{1,3} .. c_{4,3}$**:
   - `c_1_3_exact` ($2$), `c_2_3_exact` ($6$), `c_3_3_exact` ($18$) + `c_3_3_unique_18` (slice uniqueness) + **`c_4_3_exact` ($c_{4,3} = 52$)** via `third_slice_le_9`.
4. **Fujimura $S_d$-Symmetric Reduction & $d = 5, 6$ Witnesses**:
   - `fujimura_isLineFree` + `wordCard_fujimuraSet` proving **`c_5_3_ge_150`** and **`c_6_3_ge_450`**, paired with slice upper bounds **`c_5_3_upper`** ($\le 156$) and **`c_6_3_upper`** ($\le 468$).
5. **Geometric Lines & Moser Numbers $c'_{1,3} .. c'_{4,3}$**:
   - `moser_1_3_exact` ($2$), `moser_2_3_exact` ($6$), **`moser_3_3_exact` ($16$)**, **`moser_3_3_strict_gap`** ($c'_{3,3} = 16 < 18 = c_{3,3}$), **`moser_4_3_upper_48`** ($\le 48$), and **`moser_4_3_ge_43`** ($\ge 43$).
6. **Finite Coloring Bounds**:
   - `hj_two_exact` ($HJ(2, r) = r$), `hj_3_2_exact` ($HJ(3, 2) = 4$), `vdw_3_2_exact` ($W(3, 2) = 9$), **`hj_4_2_gt_4`** ($HJ(4, 2) > 4$), **`hj_3_3_gt_4`** ($HJ(3, 3) > 4$).

---

## Next Open Formalization Targets

### 1. Closing Moser $c'_{4, 3} \le 43$ via Exact Orbital LP / Farkas Certificate
- **Current status**: `43 ≤ c'_{4,3} ≤ 48` (`moser_4_3_ge_43`, `moser_4_3_upper_48`). Notice our slice bound already proves $c'_{4,3} \le 48$, while Polymath-1 proved $c'_{4,3} = 43$ via fractional line-weight duals over $[3]^4$'s geometric lines ($S_4 \times \mathbb{Z}_2$).
- **Next step**: Formalize a kernel-checked integer Farkas reflection theorem `checkFarkasMoser_sound` proving $\sum_w c_w \mathbf{1}_A(w) \le M$ from line weights $y_L \ge 0$ (`c'_{4,3} = 43` is tight in Polymath-1's LP dual + one-point branching!).

### 2. Narrowing $150 \le c_{5, 3} \le 156$ (In Fact $c_{5, 3} = 150$)
- **Current status**: `c_5_3_ge_150` and `c_5_3_upper` ($156$). Polymath-1 established $c_{5,3} = 150$ using slice stability around the $[3]^4$ extremal sets and combinatorial line double-counting.
- **Next step**: Classify 52-point and 51-point line-free slices of $[3]^4$ (analogous to `c_3_3_unique_18` via `Slice9`) to close `c_5_3_exact : c_{5,3} = 150`.

### 3. Upper Bounds for `HJ(3, 3)` and `HJ(4, 2)`
- **Current status**: Lower bounds `hj_3_3_gt_4` ($> 4$) and `hj_4_2_gt_4` ($> 4$), plus general $r$-color reflection `checkCertSym_sound`.
- **Next step**: Add coordinate-permutation symmetry breaking ($S_d$) to `CertTree` or compile SAT/DRAT-style branching trees (`HJ(3,3) ≤ 5` or `6`, `HJ(4,2)`).

### 4. Full Asymptotic Density Hales–Jewett (`DHJ(3)` / `DHJ(k)`)
- **Current status**: `dhj_two_exact` (arbitrary $d$) and `dhj_implies_hj`.
- **Next step**: Formalize Polymath-1's equal-slices / mean-square density-increment proof of asymptotic **`DHJ(3)`**, yielding an alternative density proof of `HJ(3, r)` and Roth's theorem (`r_3(N) = o(N)`) via `wordSum`.
