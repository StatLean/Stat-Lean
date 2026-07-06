import StatLean.Bayesian.Decision.BayesEstimator

/-!
# The posterior mean is the Bayes estimator under quadratic loss (Robert Proposition 2.5.1)

Under the quadratic loss `ℓ(θ, a) = (θ − a)²`, the posterior mean `x ↦ 𝔼[θ | x]` is a Bayes
estimator.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §2.5.1,
eq. (2.5.1) and Proposition 2.5.1, p. 77–78.

**Proof formalization notes.** No integrability hypothesis: we case-split on whether the posterior
`(P†π) x` has a finite second moment (`MemLp id 2`). If not, every action has infinite posterior
quadratic risk (`lintegral_sqLoss_eq_top`), so any value — including the junk `posteriorMean` — is
a pointwise minimizer; if so, the pointwise minimizer is the mean by the bias–variance inequality
(`variance_eq_integral` / `variance_sub_const` / `variance_le_expectation_sq`). The posterior is a
probability measure at every `x` (posterior Markov instance), so the split is pointwise and
`isBayesEstimator_of_ae_argmin` applies via `ae_of_all`. Bridge `‖·‖ₑ ^ 2` ↔ `(· )²` via
`Real.enorm_eq_ofReal_abs`, `ENNReal.ofReal_pow`, `sq_abs`. This subsumes Robert's "provided the
expectation exists" proviso.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- The quadratic loss is jointly measurable. -/
theorem measurable_uncurry_sqLoss : Measurable (Function.uncurry sqLoss) := sorry

/-- If the measure has no finite second moment, every action has infinite posterior quadratic
risk. -/
theorem lintegral_sqLoss_eq_top (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    -- USER-INPUT: the measure lacks a finite second moment (this branch of the case split)
    (hρ : ¬ MemLp (id : ℝ → ℝ) 2 ρ) (a : ℝ) :
    ∫⁻ θ, sqLoss θ a ∂ρ = ∞ := sorry

/-- With a finite second moment, the posterior quadratic risk is the real integral of `(θ − a)²`. -/
theorem lintegral_sqLoss_eq_ofReal_integral (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    -- USER-INPUT: the measure has a finite second moment (this branch of the case split)
    (hρ : MemLp (id : ℝ → ℝ) 2 ρ) (a : ℝ) :
    ∫⁻ θ, sqLoss θ a ∂ρ = ENNReal.ofReal (∫ θ, (θ - a) ^ 2 ∂ρ) := sorry

/-- Bias–variance inequality: the mean minimizes `a ↦ ∫ (θ − a)² dρ`. -/
theorem integral_sq_sub_integral_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    -- USER-INPUT: finite second moment (needed for the variance identity)
    (hρ : MemLp (id : ℝ → ℝ) 2 ρ) (a : ℝ) :
    ∫ θ, (θ - ∫ t, t ∂ρ) ^ 2 ∂ρ ≤ ∫ θ, (θ - a) ^ 2 ∂ρ := sorry

/-- Pointwise minimizer: the mean minimizes the quadratic posterior risk (hypothesis-free, by the
`MemLp` case split). -/
theorem lintegral_sqLoss_integral_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (a : ℝ) :
    ∫⁻ θ, sqLoss θ (∫ t, t ∂ρ) ∂ρ ≤ ∫⁻ θ, sqLoss θ a ∂ρ := sorry

/-- The posterior mean is measurable. -/
theorem measurable_posteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P]
    (π : Measure ℝ) [IsFiniteMeasure π] :
    Measurable (posteriorMean P π) := sorry

/-- **The posterior mean is a Bayes estimator under quadratic loss** (Robert Proposition 2.5.1). -/
theorem posteriorMean_isBayesEstimator_sqLoss (P : Kernel ℝ 𝓧) [IsFiniteKernel P]
    (π : Measure ℝ) [IsFiniteMeasure π] :
    IsBayesEstimator sqLoss P
      (Kernel.deterministic (posteriorMean P π) (measurable_posteriorMean P π)) π := sorry

end StatLean.Bayesian
