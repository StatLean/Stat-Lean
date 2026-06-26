import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Low-order moments of the standard Gaussian — ForMathlib brick

The first four moments of `Z ∼ N(0,1)` and the variance of `Z²`, the inputs to the chi-squared
test's mean/variance computations (Candès, Lecture 2, §2.3):

* `integral_sq_stdGaussian` — `E[Z²] = 1`;
* `integral_cube_stdGaussian` — `E[Z³] = 0` (odd moment);
* `integral_pow_four_stdGaussian` — `E[Z⁴] = 3`;
* `variance_sq_stdGaussian` — `Var[Z²] = E[(Z²−1)²] = 2`.

Under `H₀` these give `E[∑ Zᵢ²] = n`, `Var[∑ Zᵢ²] = 2n`; the `E[Z³] = 0` / `E[Z⁴] = 3` pair feed
the noncentral `H₁` moments `E[(μ+Z)²] = μ²+1`, `Var[(μ+Z)²] = 4μ²+2` in the assembly file
`ChiSquaredTest/Distribution.lean`. (`E[Z] = 0` is Mathlib's `integral_id_gaussianReal`.)

Theorem-agnostic. The χ²₁ MGF integral `∫ exp(l x²) dN(0,1) = (1−2l)^{−1/2}` and the existing
`∫ x² dN(0,1) = 1` derivation in
`HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean` are a style reference (that
file proves the second moment via `variance_fun_id_gaussianReal`).

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

/-- `E[Z²] = 1` for `Z ∼ N(0,1)`. -/
theorem integral_sq_stdGaussian : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  sorry

/-- `E[Z³] = 0` for `Z ∼ N(0,1)` (the third moment vanishes by symmetry). -/
theorem integral_cube_stdGaussian : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  sorry

/-- `E[Z⁴] = 3` for `Z ∼ N(0,1)`. -/
theorem integral_pow_four_stdGaussian : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  sorry

/-- `Var[Z²] = 2` for `Z ∼ N(0,1)`, written as the central second moment
`E[(Z²−1)²] = E[Z⁴] − 2·E[Z²] + 1 = 2`. -/
theorem variance_sq_stdGaussian : ∫ x, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1) = 2 := by
  sorry

end StatLean.MultipleTesting
