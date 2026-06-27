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

-- TODO(mmx): sparse-vector volume packing (Wainwright Ex 5.8). Over the `C(d,s)` choices of an
-- `s`-element support, run a `1/2`-separated sphere packing of the `s`-dimensional unit sphere on
-- each support (cf. `sphere_packing_card`); a counting/volume argument yields a `1/2`-separated set
-- of `s`-sparse unit vectors with `log |T| ≥ (s/2) log((d−s)/s)`. This is the genuine combinatorial
-- heart of the bound, isolated here as a single named debt.
private theorem sparse_packing (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1 ∧ (Finset.univ.filter fun i => v i ≠ 0).card ≤ s) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ :=
  sorry

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
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ :=
  sparse_packing d s hs hsd

end StatLean.Minimaxity
