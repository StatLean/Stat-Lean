# Close #5: measurable nearest-point selector (EstimationToTesting.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds. Goal 0 sorry.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/EstimationToTesting.lean`
Close the `sorry` (≈ line 139) inside `minimax_ge_testing_error`: construct
`∃ T : Ω → Fin M, Measurable T ∧ ∀ y ℓ, edist (g (θfam (T y))) y ≤ edist (g (θfam ℓ)) y`.
The signature now provides **`[OpensMeasurableSpace Ω]`** (added upstream) — USE it. Keep the public
signature/docstring UNCHANGED. **Promote the construction to a reusable**
`private lemma exists_measurable_nearestPoint` (it is consumed again by `LeCam/ConvexHull.lean`).

## Strategy
1. Each `dₗ := fun y => edist (g (θfam ℓ)) y : Ω → ℝ≥0∞` is **continuous** (`continuous_edist.comp …` / 
   `continuous_const.edist continuous_id`), hence **measurable** via `[OpensMeasurableSpace Ω]`
   (`Continuous.measurable`).
2. Define `T y` = the first index `ℓ ∈ Fin M` with `dₗ y ≤ d_k y` for all `k` (a minimizer; exists since
   `Fin M` is finite nonempty — `Finset.exists_min_image`/`Finite.exists_min`). Build it measurably with
   **`Measurable.find`** (`MeasureTheory/MeasurableSpace/Constructions.lean`): work over `ℕ` via
   `Fin.val`/`Nat.find`, predicate `p ℓ y := ∀ k, dₗ y ≤ d_k y`, whose set `{y | p ℓ y} = ⋂_k {y | dₗ y ≤ d_k y}`
   is measurable (`measurableSet_le` + finite `MeasurableSet.iInter`). Existence-of-minimizer gives the `Nat.find`
   hypothesis; cast the found `ℕ` back to `Fin M`.
3. Minimality `edist (g (θfam (T y))) y ≤ edist (g (θfam ℓ)) y` is exactly `p (T y) y` applied to `ℓ`.
Mathlib: `Measurable.find`, `measurable_find`, `measurableSet_le`, `Measurable.iInf`, `continuous_edist`,
`Continuous.measurable`, `Finset.exists_min_image`. After `⟨T, hT, hTmin⟩`, the existing final line
`exact mul_multiwayTestingError_le P hθ hΦ hsep hT hTmin` closes the theorem.

## DONE: `lake build StatLean.Minimaxity.EstimationToTesting` green, 0 sorry. `git add` ONLY that file; commit.
