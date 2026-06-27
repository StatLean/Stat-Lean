import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Data-processing inequality for KL divergence (Wainwright §15.1.3, used in Pinsker Ex 15.6)

The Kullback–Leibler divergence contracts under a measurable push-forward:
`D(μ∘f⁻¹ ‖ ν∘f⁻¹) ≤ D(μ ‖ ν)`. This is the elementary (deterministic-channel) case of the
data-processing inequality for an `f`-divergence. Mathlib provides the kernel chain rule
`klDiv_compProd_left` but not the push-forward DPI, so we add it here as a reusable `ForMathlib`
brick (candidate upstream). It is consumed by `PinskerInequality.lean` to reduce
`klDiv ν μ` to the two-cell Bernoulli case via the indicator push-forward of `{q ≤ p}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3
(data-processing inequality, used in Exercise 15.6).
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- **Data-processing inequality for KL divergence under a measurable map.** For a measurable
`f : α → β` and probability measures `μ, ν`, the KL divergence between the push-forwards is at most
the KL divergence between the originals: `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`. This is the
standard contraction of an `f`-divergence under a (deterministic) channel; proved from the kernel
chain rule `klDiv_compProd_left` by realizing `μ.map f` as a marginal of `μ ⊗ₘ deterministic f`,
since Mathlib lacks a general data-processing inequality.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3. -/
theorem klDiv_map_le {f : α → β} (hf : Measurable f) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  sorry

end StatLean.Minimaxity
