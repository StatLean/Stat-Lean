import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Packing of sparse unit vectors (Wainwright Example 5.8 / Exercise 5.8)

A Chapter-5 metric-entropy prerequisite for the sparse-linear-regression minimax lower bound
(Example 15.16): the set of `s`-sparse unit vectors in `ℝᵈ` admits a `1/2`-separated set with
```
log M ≥ (s/2) · log((d − s)/s),
```
i.e. a set `T` of `s`-sparse unit vectors, pairwise at Euclidean distance `≥ 1/2`, with
`log |T| ≥ (s/2) log((d−s)/s)`. (Sparsity: at most `s` nonzero coordinates.)

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8
(used in Chapter 15, §15.3.3, Example 15.16).
-/

open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Packing of sparse unit vectors** (Wainwright Example 5.8): the set of `s`-sparse unit
vectors in `ℝᵈ` contains a `1/2`-separated set `T` with `log |T| ≥ (s/2) log((d−s)/s)`; each
element is a unit vector with at most `s` nonzero coordinates, and any two are at Euclidean
distance `≥ 1/2`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8. -/
theorem exists_sparse_packing (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1 ∧ (Finset.univ.filter fun i => v i ≠ 0).card ≤ s) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  sorry

end StatLean.Minimaxity
