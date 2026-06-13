import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian random variables — definition

Book definition (Lu, *Big Data Analysis* §2.2, "Sub-Gaussian"): a random variable
`X` is *sub-Gaussian with variance proxy `σ²`* if
`E[exp(λ (X − E X))] ≤ exp(λ² σ² / 2)` for all `λ ∈ ℝ`.

We formalize this as a thin bridge to Mathlib's
`ProbabilityTheory.HasSubgaussianMGF` applied to the **centered** variable
`X − E[X]`. Mathlib's predicate bounds the *raw* MGF (`mgf X μ t ≤ exp (c t²/2)`,
via `cgf_le`); centering recovers the textbook form and immediately inherits the
Mathlib MGF / Chernoff / Hoeffding / Azuma toolkit.

This file is the concept-layer foundation of the `ConcentrationInequalities`
area; the textbook theorems (Markov, Chernoff, tails, Hoeffding, …) live in
sibling files and consume `IsSubGaussian`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsSubGaussian X σ2 μ`: the random variable `X` is sub-Gaussian with variance
proxy `σ2` under the measure `μ`, i.e. its centered moment generating function
satisfies `E[exp(λ (X − E[X]))] ≤ exp(λ² σ2 / 2)` for every `λ ∈ ℝ`
(Lu-BDA §2.2, "Sub-Gaussian").

Implemented as `ProbabilityTheory.HasSubgaussianMGF` of the centered variable
`fun ω => X ω − ∫ x, X x ∂μ`. The mean `∫ x, X x ∂μ` is the Bochner integral of
`X`; for non-integrable `X` it is `0` (Mathlib's junk value), in which case this
reduces to the un-centered Mathlib predicate. -/
def IsSubGaussian (X : Ω → ℝ) (σ2 : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop :=
  HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ

/-- Unfolding lemma: `IsSubGaussian` is definitionally the centered
`HasSubgaussianMGF`. -/
theorem isSubGaussian_iff {X : Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω} :
    IsSubGaussian X σ2 μ ↔ HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ :=
  Iff.rfl

end StatLean.ConcentrationInequalities
