import StatLean.ConcentrationInequalities.SubGaussian.Defs

/-!
# Bounded random variables are sub-Gaussian

Lu, *Big Data Analysis* §2.2 ("Bounded Random Variables"): if `a ≤ X ≤ b`
almost surely, then `X` is sub-Gaussian with variance proxy `(b − a)² / 4`.

The book's proxy `(b − a)² / 4` is exactly Mathlib's `(‖b − a‖₊ / 2) ^ 2`
(since `‖b − a‖₊ = |b − a|` and `|b − a|² = (b − a)²`). This is a direct
consequence of Mathlib's Hoeffding lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, which already centers by the
mean — matching our `IsSubGaussian` (centered `HasSubgaussianMGF`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A bounded random variable `a ≤ X ≤ b` (a.s.) is sub-Gaussian with variance
proxy `(b − a)² / 4`, written `(‖b − a‖₊ / 2) ^ 2` (Lu-BDA §2.2,
"Bounded Random Variables"). -/
theorem isSubGaussian_of_mem_Icc {X : Ω → ℝ} {a b : ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    -- USER-INPUT: X is (a.e.-)measurable; Lu-BDA §2.2 (regularity, implicit in the book).
    (hm : AEMeasurable X μ)
    -- USER-INPUT: a ≤ X ≤ b almost surely; Lu-BDA §2.2 hypothesis.
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    IsSubGaussian X ((‖b - a‖₊ / 2) ^ 2) μ :=
  hasSubgaussianMGF_of_mem_Icc hm hb

end StatLean.ConcentrationInequalities
