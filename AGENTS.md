# Agent Guide for `hj-brigade`

When developing or proving new Ramsey Theory / Hales–Jewett theorems in this repository (whether using an interactive coding agent such as Antigravity / Claude Code / Cursor, or an automated proving pipeline), follow this workflow:

## 1. Core Library Modules (`HJBrigade`)
Before creating new definitions, query what is already compiled:
```bash
python scripts/run_cli.py index --query "<keyword>"
```
Key canonical objects (`import HJBrigade` + `open HJBrigade`):
- `Word d k` (`Fin d → Fin k`), `Line d k`, `HJUpper d k r`, `HJUpper.mono_dim`, `HJUpper.mono_colors`
- `FinEquiv`, `finEquivFun`, `encodeMap`, `encodeMap_inj`, `fin_pigeonhole`
- `hj_two_upper`, `hj_two_lower`, `hj_two_exact`
- `CombSubspace`, `ColorFocusedLines`, `color_focused_dichotomy`
- `shelahCubeDim`, `shelahHJDim`, `shelah_equal_ends`, `hales_jewett_shelah`, `hales_jewett`, `van_der_waerden`
- `IsMonoSubspace`, `MHJUpper`, `mhjDim`, `mhj_shelah`, `multidimensional_hales_jewett`
- `wordCard`, `IsLineFree`, `lineFree_slice_bound`, `dhj_implies_hj`, `sperner_dhj_two`, `dhj_two_exact`
- `c_1_3_exact`, `c_2_3_exact`, `c_3_3_exact`, `c_4_3_ge_52`
- `CertTree`, `checkCert_sound`, `checkCertSym2_sound`, `checkCertSym_sound`

## 2. Interactive Blueprint Loop (Best Practice for Hard Proofs)
1. Write a draft Lean file with `theorem ... := by sorry` subgoals.
2. Run:
   ```bash
   python scripts/run_cli.py blueprint path/to/Draft.lean
   ```
   This compiles the file once, extracts exact elaborated `⊢` goal states for every `sorry`, retrieves matching `HJBrigade` lemmas, and runs `#print axioms` on completed theorems.
3. For finite coloring or density claims, NEVER brute-force by hand — compile a kernel-checked witness/certificate first:
   ```bash
   python scripts/run_cli.py certify-hj --d 4 --k 3 --r 2 --verify
   python scripts/run_cli.py certify-dhj --d 4 --k 3 --verify
   ```

## 3. Non-Negotiable Soundness Rules
- **Zero `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `partial`, or `native_decide`** in committed Lean files.
- **Only kernel-checked `decide`** and standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) are permitted.
- Always run `lake build` and `python scripts/run_cli.py audit-repo` before committing.
