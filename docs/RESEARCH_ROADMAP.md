# Open Research & Formalization Roadmap

`HJBrigade` provides an axiom-clean, zero-Mathlib Lean 4 foundation for Hales–Jewett theory. Below are concrete open formalization milestones and research problems suited to combining interactive Lean agents with combinatorial certificate compilers:

## 1. Closing Polymath-1 $c_{4, 3} \le 52$ in Lean's Kernel
- **Current status in `HJBrigade/Density/ExactDHJ.lean`**:
  - `c_1_3_exact`: $c_{1,3} = 2$
  - `c_2_3_exact`: $c_{2,3} = 6$
  - `c_3_3_exact`: $c_{3,3} = 18$
  - `c_4_3_ge_52`: Explicit 52-element line-free subset of $[3]^4$ verified in Lean's kernel.
- **Next step**: Formalize the **equal-weight LP dual / Farkas certificate** (Polymath-1 proved $c_{4,3} = 52$ via fractional weights over $S_4 \times S_3$ symmetry orbits of $[3]^4$, reducing 81 vertices and 175 lines to a small integer dual witness `(w : Word 4 3 → Nat, c : Line 4 3 → Nat)` verifying $\sum_{w \in \text{line}} \text{coeff} \ge \text{RHS}$). A reflection theorem `checkFarkasDHJ_sound` (analogous to `checkCertSym_sound`) would close `c_4_3_exact : c_{4,3} = 52` purely inside Lean's kernel!

## 2. Exact Coloring Bounds Beyond `HJ(3, 2) = 4`
- **Current status**: `HJ(2, r) = r` proved for all $r \ge 1$ (`hj_two_exact`); `HJ(3, 2) = 4` (`hj_3_2_exact`); general $r$-color symmetry reflection (`checkCertSym_sound`) proved.
- **Open targets**:
  - Machine-check $HJ(3, 3)$ bounds: lower bound search ($[3]^d$ with 3 colors; note Hindman–Tressler bounds) and SAT/DRAT-style reflection checking (`CertTree` + symmetry under $S_d \times S_3$!) for `HJUpper d 3 3`.
  - Machine-check $HJ(4, 2)$ bounds (note $HJ(4, 2) > 5$ vs upper bounds via symmetry-broken CDCL certificates).

## 3. Full Asymptotic Density Hales–Jewett (`DHJ(3)` / `DHJ(k)`)
- **Current status**: `dhj_two_exact` (exact $c_{d, 2} = \binom{d}{\lfloor d/2 \rfloor}$ via constructive Symmetric Chain Decomposition) and `dhj_implies_hj` (density $\implies$ coloring transfer).
- **Next step**: Formalize Polymath-1's elementary density-increment proof of **`DHJ(3)`** (mean-square / equal-slices entropy or combinatorial density increment on $[3]^d$), then connect `dhj_implies_hj` to obtain a **density proof of `HJ(3, r)`** and **Roth's theorem (`r_3(N) = o(N)`)** via `wordSum`!

## 4. Tightening `shelahHJDim` & Mathlib Interop
- Optimize `shelahCubeDim` / `shelahHJDim` (currently explicit primitive-recursive tower) and establish the `HJBrigade.Line d k ≃ Combinatorics.Line (Fin k) (Fin d)` bridge described in [MATHLIB_BRIDGE.md](MATHLIB_BRIDGE.md).

## 5. Geometric Lines (Moser Numbers $c'_{d, k}$)
- Extend `Line d k` to **geometric lines** (`±1` direction vectors in $[k]^d$ as well as `+1` combinatorial lines) and compile exact Moser witnesses & Farkas upper certificates for $c'_{d, 3}$ ($c'_{1,3}=2, c'_{2,3}=6, c'_{3,3}=16, c'_{4,3}=43$).
