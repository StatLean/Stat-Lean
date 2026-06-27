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

-- TODO(mmx): volume/sphere-counting packing (Wainwright Ex 5.8), cardinality form. For `n ≥ 1`
-- there are at least `2^n` unit vectors of `ℝⁿ` that are pairwise `≥ 1/2`-separated: take a maximal
-- `1/2`-separated subset of the unit sphere; the disjoint radius-`1/4` balls around its points sit
-- inside the radius-`5/4` ball, and `1/2`-balls around them cover the sphere, giving a count
-- exponential in `n` with base `> 2`. This is the genuine combinatorial heart, isolated as a debt.
private theorem sphere_packing_card (n : ℕ) (hn : 1 ≤ n) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (2 : ℝ) ^ n ≤ (T.card : ℝ) ∧
      (∀ v ∈ T, ‖v‖ = 1) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ :=
  sorry

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
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: no unit vectors exist, but the bound is `0 ≤ log 0 = 0`, so the empty set works.
    subst hn
    refine ⟨∅, ?_, ?_, ?_⟩
    · simp
    · intro v hv; simp at hv
    · intro u hu; simp at hu
  · -- `n ≥ 1`: derive the `log` bound from the cardinality crux via monotonicity of `log`.
    obtain ⟨T, hcard, hnorm, hsep⟩ := sphere_packing_card n hn
    refine ⟨T, ?_, hnorm, hsep⟩
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h := Real.log_le_log hpos hcard
    rwa [Real.log_pow] at h

end StatLean.Minimaxity
