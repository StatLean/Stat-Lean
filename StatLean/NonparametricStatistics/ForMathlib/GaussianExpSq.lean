import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

/-!
# Gaussian exponential-square moments and weighted sums

Two Gaussian facts feeding the sup-norm risk analysis of linear smoothers:

* `lintegral_exp_mul_sq_gaussianReal_le` — for `X ~ N(0, v)` and `4av ≤ 1`:
  `E[exp(a·X²)] ≤ √2` (the classical `α₀ = 1/(4σ²)` exponential-square moment bound).
* `hasLaw_sum_mul_gaussianReal` — a linear combination `∑ cᵢ·ξᵢ` of independent `N(0, v)`
  variables is `N(0, (∑ cᵢ²)·v)`.

**Proof formalization notes.** The exponential-square moment is the explicit Gaussian integral
`E exp(aX²) = (1 − 2av)^{-1/2}`, computed from the density (`gaussianPDFReal`) and
`integral_gaussian`-family lemmas; at `4av ≤ 1` the value is at most `√2`, and for `a ≤ 0` the
integrand is bounded by `1`. The `v = 0` case is the Dirac mass, where the integral is `1`.
The weighted-sum law is induction on the index set via
`ProbabilityTheory.gaussianReal_conv_gaussianReal` (convolution of Gaussians), the map lemma
`gaussianReal_map_const_mul` for the scalar factors, and independence of the partial sum from
the next coordinate (`iIndepFun.indepFun_finset_sum_of_notMem`-style); zero coefficients
degrade gracefully since `N(0,0) = δ₀`.

**Bibliographic comments.** Classical Gaussian computations; the exponential-square moment in
this normalized form is folklore (see e.g. relevant chapters of textbooks on Gaussian
processes).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Exponential-square moment of a centered Gaussian**: for `X ~ N(0, v)` and `4·a·v ≤ 1`,
`E[exp(a·X²)] ≤ √2`. (For `a ≤ 0` the bound is trivial; at `a = 1/(4v)` the exact value is
`(1 − 1/2)^{-1/2} = √2`.) -/
theorem lintegral_exp_mul_sq_gaussianReal_le (v : ℝ≥0) {a : ℝ}
    -- USER-INPUT: the exponent scale satisfies `4·a·v ≤ 1`; classical range of the Gaussian
    -- exponential-square moment
    (ha : a * (4 * (v : ℝ)) ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂(gaussianReal 0 v)
      ≤ ENNReal.ofReal (Real.sqrt 2) := by
  sorry

/-- **Weighted sums of independent centered Gaussians are Gaussian**:
if `ξ 0, …, ξ (n−1)` are independent with common law `N(0, v)`, then
`∑ i, c i · ξ i` has law `N(0, (∑ i, c i²)·v)`. -/
theorem hasLaw_sum_mul_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ} {v : ℝ≥0} (c : Fin n → ℝ)
    -- LEAN-ONLY: measurability of the coordinates; standard regularity
    (hmeas : ∀ i, Measurable (ξ i))
    -- USER-INPUT: mutual independence of the noise coordinates; classical Gaussian-sum input
    (hindep : iIndepFun ξ P)
    -- USER-INPUT: each coordinate is centered Gaussian with variance `v`
    (hlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) :
    HasLaw (fun ω => ∑ i, c i * ξ i ω)
      (gaussianReal 0 ((∑ i, (c i) ^ 2 : ℝ).toNNReal * v)) P := by
  sorry

end StatLean.NonparametricStatistics
