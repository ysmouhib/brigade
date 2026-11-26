# Bridging `HJBrigade` to `Mathlib.Combinatorics.HalesJewett`

`HJBrigade` intentionally compiles in **~3 seconds on standalone Lean 4.35.0** with zero multi-gigabyte Mathlib cache dependency so the proving brigade, reflection checker, and test suite iterate instantaneously.

When scaling to infinite-type asymptotic proofs (such as Shelah's primitive-recursive `ack_5` bound or full multidimensional Hales–Jewett), every core definition in `HJBrigade` aligns 1-to-1 with `Mathlib.Combinatorics.HalesJewett`:

| `HJBrigade` Symbol | `Mathlib.Combinatorics.HalesJewett` Equivalent | Notes |
| --- | --- | --- |
| `Word d k` (`Fin d → Fin k`) | `ι → α` (`[Fintype ι] [Fintype α]`) | Finite hypercube over `Fin d` and `Fin k` |
| `Line d k` (`mask : Fin d → Option (Fin k)`, `hasWildcard`) | `Combinatorics.Line α ι` (`idxFun`, `proper`) | Identical `Option` mask representation (`none` = wildcard, `some a` = constant) |
| `Line.eval L t` | `L t` (`FunLike.coe`) | Pointwise `(mask i).getD t` |
| `IsMonoLine c L` | `∃ c₀, ∀ t, C (L t) = c₀` | Monochromatic combinatorial line |
| `HJUpper d k r` | `∀ C : (Fin d → Fin k) → Fin r, ∃ L c₀, ∀ t, C (L t) = c₀` | Specialization of `Combinatorics.Line.exists_mono_in_high_dimension` |
| `CombSubspace m d k` | Subcube embedding `Fin m → Option ...` / `Line.horizontal` | Maps lower-dimensional lines into higher-dimensional spaces |
| `ColorFocusedLines s d k` | `Combinatorics.Line.AlmostMono` | Lines monochromatic on `Fin (k - 1)` meeting at focus `k - 1` |
| `hj_implies_vdw` | `Combinatorics.exists_mono_homothetic_copy` | Coordinate-sum homomorphism `(Fin d → Fin (k+1)) →+ ℕ` |

## Connecting Mathlib (Optional)

Run `scripts/enable_mathlib.ps1` (after checking your `lean-toolchain` vs Mathlib tag) to add `Mathlib` as a `lakefile.toml` dependency and fetch prebuilt `.olean` caches (`lake exe cache get`). Once `import Mathlib.Combinatorics.HalesJewett` is active, a 15-line equivalence wrapper transports `HJBrigade.Line d k ≃ Combinatorics.Line (Fin k) (Fin d)` without changing any downstream theorems in `HJBrigade`.

Related formalizations for advanced bounds:
- `Mathlib.Combinatorics.HalesJewett` (color-focusing proof + Van der Waerden corollary)
- `gdahia/ShelahHalesJewett` (Saharon Shelah's explicit `ack_5` primitive-recursive bound in Lean 4)
