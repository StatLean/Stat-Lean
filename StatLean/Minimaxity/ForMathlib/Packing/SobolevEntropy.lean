import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Metric entropy of the Sobolev ellipsoid (Wainwright Example 5.12)

A Chapter-5 metric-entropy prerequisite for the Sobolev minimax example (15.23). For smoothness
`α > 1/2`, the Sobolev ellipsoid `ℰ_α = {θ ∈ ℓ²(ℕ) : Σⱼ j^{2α} θⱼ² ≤ 1}` has metric entropy
```
log N(δ; ℱ_α, ‖·‖₂) ≍ (1/δ)^{1/α}                       (Example 5.12),
```
the Kolmogorov–Tikhomirov rate. The minimax lower bounds need the packing (lower) direction.

⚠ **Research-grade (◆◆).** Time-boxed; if it resists, escalate as a named debt per CLAUDE.md §2.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.12
(used in Chapter 15, §15.3.5, Example 15.23).
-/

open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Packing lower bound for the Sobolev ellipsoid** (Wainwright Example 5.12): for `α > 1/2` and
`0 < δ`, the ellipsoid `ℰ_α ⊂ ℓ²(ℕ)` contains a `δ`-separated set `T` with
`log |T| ≳ (1/δ)^{1/α}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.12. -/
theorem sobolev_packing_lower_bound (α : ℝ) (hα : 1 / 2 < α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (c : ℝ) (_ : 0 < c) (T : Finset (lp (fun _ : ℕ => ℝ) 2)),
      c * (1 / δ) ^ (1 / α) ≤ Real.log T.card ∧
      (∀ x ∈ T, ∑' j : ℕ, ((j : ℝ) + 1) ^ (2 * α) * (x j) ^ 2 ≤ 1) ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ ‖x - y‖ := by
  sorry

end StatLean.Minimaxity
