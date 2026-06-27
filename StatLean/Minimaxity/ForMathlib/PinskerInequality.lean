import StatLean.Minimaxity.ForMathlib.TotalVariation
import StatLean.Minimaxity.ForMathlib.KLDivergence

/-!
# Pinsker–Csiszár–Kullback inequality — Lemma 15.2 (Wainwright §15.1.3)

The total variation distance is controlled by the Kullback–Leibler divergence:
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`  (Eq. (15.8)).

Wainwright outlines the proof in Exercise 15.6: reduce to the Bernoulli case via the partition
`A = {p ≥ q}` and Jensen's inequality. We state it with the `ℝ≥0∞` square root (`rpow (1/2)`),
so the bound is vacuously true when the KL divergence is infinite.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Bernoulli crux of Pinsker's inequality** (Wainwright Exercise 15.6).

With densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`, the half-`L¹` form of total variation
is bounded by the KL divergence through the data-processing reduction to the Bernoulli partition
`A = {p ≥ q}` and the pointwise inequality
`2 (δ_p − δ_q)² ≤ δ_p log(δ_p/δ_q) + (1 − δ_p) log((1 − δ_p)/(1 − δ_q))` followed by Jensen.
This is the genuine analytic core; the public theorem `pinsker_tv_le_kl` follows by the density
form `tvDist_eq_half_lintegral`. -/
private lemma pinsker_half_lintegral_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  sorry -- TODO(mmx): Ex 15.6 — Bernoulli reduction (partition {p≥q}) + pointwise bound + Jensen

/-- **Pinsker–Csiszár–Kullback inequality** (Wainwright Lemma 15.2, Eq. (15.8)):
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2. -/
theorem pinsker_tv_le_kl (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [tvDist_eq_half_lintegral]
  exact pinsker_half_lintegral_le μ ν

end StatLean.Minimaxity
