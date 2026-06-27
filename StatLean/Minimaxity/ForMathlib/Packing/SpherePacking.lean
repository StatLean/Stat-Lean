import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Packing of the Euclidean unit sphere (Wainwright Example 5.8)

A Chapter-5 metric-entropy prerequisite for the PCA minimax lower bound (Example 15.19): the unit
sphere of `ℝⁿ` admits a `1/2`-separated set of exponentially large cardinality,
```
log M(1/2; 𝕊ⁿ⁻¹, ‖·‖₂) ≥ n · log 2                    (Example 5.8)
```
i.e. a set `T` of unit vectors, pairwise at Euclidean distance `≥ 1/2`, with `log |T| ≥ n·log 2`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8
(used in Chapter 15, §15.3.4, Example 15.19).
-/

open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Packing of the Euclidean unit sphere** (Wainwright Example 5.8): the unit sphere of `ℝⁿ`
contains a `1/2`-separated set `T` (pairwise Euclidean distance `≥ 1/2`) of unit vectors with
`log |T| ≥ n · log 2`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8. -/
theorem exists_sphere_packing (n : ℕ) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (n : ℝ) * Real.log 2 ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  sorry

end StatLean.Minimaxity
