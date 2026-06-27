import StatLean.Minimaxity.ForMathlib.TotalVariation
import StatLean.Minimaxity.ForMathlib.HellingerDivergence

/-!
# Le Cam's inequality — Lemma 15.3 (Wainwright §15.1.3)

The total variation distance is controlled by the Hellinger distance:
`‖ℙ − ℚ‖_TV ≤ H(ℙ ‖ ℚ) · √(1 − H²(ℙ ‖ ℚ)/4)`  (Eq. (15.10)),

where `H = √(H²)` is the (unsquared) Hellinger distance. Wainwright works through the proof in
Exercise 15.5 (Cauchy–Schwarz on `(√p − √q)(√p + √q)`). We use the `ℝ≥0∞` square root `rpow (1/2)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.3.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Cauchy–Schwarz crux of Le Cam's inequality** (Wainwright Exercise 15.5).

Writing `p = dℙ/dξ`, `q = dℚ/dξ` for the densities against `ξ = ℙ + ℚ`, the half-`L¹` form of
total variation is bounded by the Hellinger product via Cauchy–Schwarz on the factorization
`|p − q| = |√p − √q| · (√p + √q)`:
`½ ∫ |p − q| dξ ≤ ½ √(∫ (√p − √q)² dξ) · √(∫ (√p + √q)² dξ)`,
and `∫ (√p + √q)² dξ = 2 + 2 ∫ √(pq) dξ = 4 − H²`, giving the stated bound. This is the genuine
analytic core; the public theorem `lecam_tv_le_hellinger` follows by the density form
`tvDist_eq_half_lintegral`. -/
private lemma lecam_half_lintegral_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      ≤ (sqHellinger μ ν) ^ (1 / 2 : ℝ) * (1 - sqHellinger μ ν / 4) ^ (1 / 2 : ℝ) := by
  sorry -- TODO(mmx): Ex 15.5 — Cauchy–Schwarz on |√p−√q|·(√p+√q) with ∫(√p+√q)² = 4 − H²

/-- **Le Cam's inequality** (Wainwright Lemma 15.3, Eq. (15.10)):
`‖ℙ − ℚ‖_TV ≤ H(ℙ ‖ ℚ) · √(1 − H²(ℙ ‖ ℚ)/4)`, with `H = √(H²)` the Hellinger distance.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.3. -/
theorem lecam_tv_le_hellinger (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν
      ≤ (sqHellinger μ ν) ^ (1 / 2 : ℝ) * (1 - sqHellinger μ ν / 4) ^ (1 / 2 : ℝ) := by
  rw [tvDist_eq_half_lintegral]
  exact lecam_half_lintegral_le μ ν

end StatLean.Minimaxity
