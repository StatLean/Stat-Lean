import StatLean.MultipleTesting.ForMathlib.GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Chi-squared test statistic — mean and variance under H₀ and H₁ (Candès L2 §2.3)

The chi-squared goodness-of-fit test for the Gaussian sequence model `Yᵢ = θᵢ + zᵢ`,
`zᵢ ∼ N(0,1)` i.i.d., with statistic `Tₙ = ∑ᵢ Yᵢ² = ‖Y‖²`. The mean and variance of `Tₙ` (Candès,
Lecture 2, §2.3) — the inputs to the power analysis via the signal-to-noise ratio
`θₙ = ‖θ‖/√(2n)`:

* **Under H₀** (`θ = 0`, `Tₙ = ∑ zᵢ²`): `E[Tₙ] = n`, `Var[Tₙ] = 2n`;
* **Under H₁** (`Tₙ = ∑ (θᵢ+zᵢ)²`): `E[Tₙ] = n + ‖θ‖²`, `Var[Tₙ] = 2n + 4‖θ‖²`
  (`‖θ‖² = ∑ᵢ θᵢ²`).

The per-coordinate moments `E[z²]=1, E[z³]=0, E[z⁴]=3, Var[z²]=2` come from the merged
`ForMathlib/GaussianMoments.lean`; the sums use linearity and (for the variances) independence
across coordinates, so the cross-covariances vanish. (The exact law `Tₙ ∼ χ²ₙ` under H₀ is
`ForMathlib/ChiSquared.map_sum_sq_eq_chiSquared`; the `n→∞` CLT normal approximation is a separate
asymptotic statement.)

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- **χ² statistic mean under H₀**: `E[∑ zᵢ²] = n` for `zᵢ ∼ N(0,1)` i.i.d. (Candès L2 §2.3). -/
theorem chiSq_H0_mean (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1) :
    ∫ ω, ∑ i, (z i ω) ^ 2 ∂P = (n : ℝ) := by
  sorry

/-- **χ² statistic variance under H₀**: `Var[∑ zᵢ²] = 2n` for `zᵢ ∼ N(0,1)` i.i.d. (Candès L2 §2.3). -/
theorem chiSq_H0_variance (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1)
    -- USER-INPUT: the zᵢ are jointly independent; Candès L2 §2.3
    (hindep : iIndepFun z P) :
    ∫ ω, (∑ i, (z i ω) ^ 2 - (n : ℝ)) ^ 2 ∂P = 2 * (n : ℝ) := by
  sorry

/-- **χ² statistic mean under H₁**: `E[∑ (θᵢ+zᵢ)²] = n + ‖θ‖²` (Candès L2 §2.3). -/
theorem chiSq_H1_mean (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ) (θ : Fin n → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1) :
    ∫ ω, ∑ i, (θ i + z i ω) ^ 2 ∂P = (∑ i, (θ i) ^ 2) + (n : ℝ) := by
  sorry

/-- **χ² statistic variance under H₁**: `Var[∑ (θᵢ+zᵢ)²] = 2n + 4‖θ‖²` (Candès L2 §2.3). -/
theorem chiSq_H1_variance (P : Measure Ω) [IsProbabilityMeasure P] (z : Fin n → Ω → ℝ)
    (θ : Fin n → ℝ)
    -- USER-INPUT: each zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (z i))
    -- USER-INPUT: each zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (z i) P = gaussianReal 0 1)
    -- USER-INPUT: the zᵢ are jointly independent; Candès L2 §2.3
    (hindep : iIndepFun z P) :
    ∫ ω, (∑ i, (θ i + z i ω) ^ 2 - ((∑ i, (θ i) ^ 2) + (n : ℝ))) ^ 2 ∂P
      = 2 * (n : ℝ) + 4 * (∑ i, (θ i) ^ 2) := by
  sorry

end StatLean.MultipleTesting
