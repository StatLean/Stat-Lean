import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# MGF of a squared standard Gaussian — ForMathlib brick

The moment generating function of `Z²` for `Z ∼ N(0,1)`, the analytic input to identifying the
chi-squared law `∑ᵢ Zᵢ² ∼ χ²ₙ` (Candès, Lecture 2, §2.3):

* `mgf_exp_sq_stdGaussian` — `∫ exp(l·x²) dN(0,1) = (1 − 2l)^{−1/2}` for `l < 1/2`;
* `integrable_exp_sq_stdGaussian` — integrability of `x ↦ exp(l·x²)` under `N(0,1)` for `l < 1/2`.

(This re-derives, as a public `ForMathlib` lemma, the closed form proved `private`ly as
`integral_exp_mul_sq_stdGaussian` in `HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean`
— that file is a concept-layer module and cannot be imported upward.) Consumed by
`ForMathlib/ChiSquared.map_sum_sq_eq_chiSquared`.

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory Real

namespace StatLean.MultipleTesting

/-- **Squared-Gaussian MGF integral**: `∫ exp(l·x²) dN(0,1) = (1 − 2l)^{−1/2}` for `l < 1/2`
(i.e. `(√(1−2l))⁻¹`). The closed form of the χ²₁ moment generating function. -/
theorem mgf_exp_sq_stdGaussian {l : ℝ} (hl : l < 1 / 2) :
    ∫ x, Real.exp (l * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * l))⁻¹ := by
  sorry

/-- Integrability of `x ↦ exp(l·x²)` under the standard Gaussian, for `l < 1/2`. -/
theorem integrable_exp_sq_stdGaussian {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x => Real.exp (l * x ^ 2)) (gaussianReal 0 1) := by
  sorry

end StatLean.MultipleTesting
