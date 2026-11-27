# Bridging `HJBrigade` to `Mathlib.Combinatorics.HalesJewett`

`HJBrigade` intentionally compiles quickly on standalone **Lean 4.35.0** with zero Mathlib cache download so the proving brigade, kernel reflection checkers (`CertTree` and `HyperCert`), and CI test suite iterate rapidly.

When extending `HJBrigade` alongside Mathlib (for infinite-type asymptotics or number-theoretic density results), every core structure aligns cleanly with `Mathlib`:

| `HJBrigade` Symbol | Status in `HJBrigade` | `Mathlib` Counterpart / Bridge Notes |
| --- | --- | --- |
| `Word d k` (`Fin d → Fin k`) | Proved & active | `ι → α` (`[Fintype ι] [Fintype α]`) |
| `Line d k` (`mask : Fin d → Option (Fin k)`, `hasWildcard`) | Proved & active | `Combinatorics.Line α ι` (`idxFun`, `proper`) |
| `IsMonoLine c L`, `HJUpper d k r` | Proved & active (`hales_jewett_shelah`, `hales_jewett`) | `Combinatorics.Line.exists_mono_in_high_dimension` |
| `CombSubspace m d k`, `MHJUpper m D k r` | Proved & active (`mhj_shelah`, `multidimensional_hales_jewett`) | Multidimensional Hales–Jewett subcube embeddings |
| `ColorFocusedLines s d k` | Proved & active (`color_focused_dichotomy`) | `Combinatorics.Line.AlmostMono` |
| `hj_implies_vdw`, `van_der_waerden` | Proved & active | `Combinatorics.exists_mono_homothetic_copy` |
| `HasMonoSchur`, `multicolor_ramsey_implies_schur`, `schur_theorem` | Proved & active | Difference coloring from multicolor triangles |
| `GraphRamseyUpper`, `MulticolorRamseyUpper` | Proved & active (`erdos_szekeres`, `erdos_szekeres_even`) | Finite simple-graph edge Ramsey bounds (`SimpleGraph`) |

## Connecting Mathlib (Optional)

Run [scripts/enable_mathlib.ps1](../scripts/enable_mathlib.ps1) (checking your `lean-toolchain` vs Mathlib release tag) to add `Mathlib` as a `lakefile.toml` dependency and fetch prebuilt `.olean` caches (`lake exe cache get`). Once `import Mathlib.Combinatorics.HalesJewett` is active, a small equivalence wrapper transports `HJBrigade.Line d k ≃ Combinatorics.Line (Fin k) (Fin d)` without changing any existing `HJBrigade` theorems.
