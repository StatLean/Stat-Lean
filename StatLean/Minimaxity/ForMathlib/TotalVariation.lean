import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Total variation distance between probability measures (Wainwright §15.1.3)

Mathlib has the *signed-measure* (Jordan) total variation, but no total-variation **distance
between two probability measures**. We define it via Wainwright's supremum form (Eq. (15.5)),

`tvDist ℙ ℚ = sup_{A measurable} (ℙ(A) − ℚ(A))`  (truncated subtraction in `ℝ≥0∞`),

which equals `sup_A |ℙ(A) − ℚ(A)|` (taking the complement flips the sign), and prove:

* `tvDist_le_one` — `tvDist ℙ ℚ ≤ 1` for probability measures;
* `tvDist_comm` — symmetry;
* `tvDist_eq_half_lintegral` — the density form `tvDist ℙ ℚ = ½ ∫ |p − q| dν` (Eq. (15.6));
* `one_sub_tvDist_eq_iInf` — the variational representation
  `1 − tvDist ℙ ℚ = inf_{f₀+f₁ ≥ 1} (∫ f₀ dℙ + ∫ f₁ dℚ)` (Exercise 15.1), used for Le Cam's
  convex-hull bound (Lemma 15.9).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.5)–(15.6).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Total variation distance** between two measures (Wainwright Eq. (15.5)):
`‖ℙ − ℚ‖_TV = sup_{A} (ℙ(A) − ℚ(A))` with truncated subtraction in `ℝ≥0∞`. For probability
measures this equals `sup_A |ℙ(A) − ℚ(A)|` and lies in `[0,1]`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.5). -/
noncomputable def tvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_ : MeasurableSet s), μ s - ν s

/-- Total variation distance is symmetric. -/
theorem tvDist_comm (μ ν : Measure α) : tvDist μ ν = tvDist ν μ := by
  sorry

/-- For probability measures, `tvDist ℙ ℚ ≤ 1`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3. -/
theorem tvDist_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  sorry

/-- **Density (one-half `L¹`) form of total variation** (Wainwright Eq. (15.6)):
`‖ℙ − ℚ‖_TV = ½ ∫ |p − q| dν`, here with the common dominating measure `ξ = ℙ + ℚ` and
densities `p = dℙ/dξ`, `q = dℚ/dξ`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.6). -/
theorem tvDist_eq_half_lintegral (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν
      = 2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν) := by
  sorry

/-- **Variational representation of total variation** (Wainwright Exercise 15.1):
`1 − ‖ℙ − ℚ‖_TV = inf { ∫ f₀ dℙ + ∫ f₁ dℚ : f₀, f₁ ≥ 0 measurable, f₀ + f₁ ≥ 1 pointwise }`.
This is the form used in the proof of Le Cam's convex-hull bound (Lemma 15.9).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.1. -/
theorem one_sub_tvDist_eq_iInf (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - tvDist μ ν
      = ⨅ (f₀ : α → ℝ≥0∞) (f₁ : α → ℝ≥0∞) (_ : Measurable f₀) (_ : Measurable f₁)
          (_ : ∀ x, 1 ≤ f₀ x + f₁ x),
          (∫⁻ x, f₀ x ∂μ + ∫⁻ x, f₁ x ∂ν) := by
  sorry

end StatLean.Minimaxity
