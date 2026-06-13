import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Regular estimator sequence

The definition `RegularEstimatorSequence` underlying vdV §8.5 Theorem 8.8
("Convolution Theorem"): an estimator sequence `T_n` is regular at `θ` for
estimating `ψ(θ)` if, for every `h`,
`√n (T_n − ψ(θ + h/√n)) ⇝ L_θ` under `P^n_{θ + h/√n}`, with the limit
distribution `L_θ` the same probability measure for every `h`.

The 8.8 main theorem and assembly glue live in `Ch8/HajekLeCamConvolution.lean`.

Headline declaration: `RegularEstimatorSequence`.
-/

open MeasureTheory

namespace AsymptoticStatistics
namespace ParametricFamily

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Regular estimator sequence at `θ₀`** (vdV §8.5).

`T n : (Fin n → 𝓧) → ℝᵈ` is a regular estimator sequence for `ψ(θ)` at
`θ₀` iff there exists a probability measure `L_θ` on `ℝᵈ` (the **limit
distribution**) such that for every `h ∈ ℝᵏ`,
$$\sqrt n\, (T_n - \psi(\theta_0 + h/\sqrt n)) \xrightarrow{P^n_{\theta_0 + h/\sqrt n}} L_\theta.$$

Crucially, `L_θ` is **independent of `h`** — that is the *regularity* part.

Encoding notes:
* `productMeasure M μ θ n` is the `n`-fold product measure of `μ.withDensity
  M.density θ` (see `Ch7/AsymptoticRepresentation.lean`).
* Weak convergence is via the project's `WeakConverges` test-function form
  (`ForMathlib/Contiguity.lean`).
* The `limitDist` field is the same as vdV's `L_θ`; `tendsto` IS vdV's
  defining clause.

vdV §8.5: removing either `limitDist` or `tendsto` would not be a
`RegularEstimatorSequence`. The `isProb` field is the "probability measure"
qualifier vdV's text demands explicitly. -/
structure RegularEstimatorSequence
    (M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)) (μ : Measure 𝓧)
    (θ₀ : AsymptoticRepresentation.Θ k)
    (ψ : AsymptoticRepresentation.Θ k → AsymptoticRepresentation.𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → AsymptoticRepresentation.𝓨 d) : Type where
  /-- vdV §8.5: the common limit distribution `L_θ` (independent of `h`). -/
  limitDist : Measure (AsymptoticRepresentation.𝓨 d)
  /-- vdV §8.5: `L_θ` is a probability measure. -/
  isProb : IsProbabilityMeasure limitDist
  /-- vdV §8.5: for every `h ∈ ℝᵏ`, the rescaled
  recentred statistic `√n (T_n − ψ(θ₀ + h/√n))` weakly converges to
  `limitDist` under `P^n_{θ₀ + h/√n}`. -/
  tendsto : ∀ h : AsymptoticRepresentation.Θ k,
    WeakConverges
      (fun n : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map
          (fun x => (Real.sqrt n) •
            (T n x - ψ (θ₀ + (Real.sqrt n)⁻¹ • h))))
      limitDist

/-- The `limitDist` of a `RegularEstimatorSequence` is a probability measure. -/
instance RegularEstimatorSequence.isProbabilityMeasure_limitDist
    {M : ParametricFamily 𝓧 (AsymptoticRepresentation.Θ k)} {μ : Measure 𝓧}
    {θ₀ : AsymptoticRepresentation.Θ k}
    {ψ : AsymptoticRepresentation.Θ k → AsymptoticRepresentation.𝓨 d}
    {T : ∀ n, (Fin n → 𝓧) → AsymptoticRepresentation.𝓨 d}
    (hReg : RegularEstimatorSequence M μ θ₀ ψ T) :
    IsProbabilityMeasure hReg.limitDist :=
  hReg.isProb

end ParametricFamily
end AsymptoticStatistics
