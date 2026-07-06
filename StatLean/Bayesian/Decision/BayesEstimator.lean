import StatLean.Bayesian.Decision.Defs

/-!
# Bayes estimators via posterior-risk minimization (Robert Theorem 2.3.2)

Our own formalization of Robert's Theorem 2.3.2 and Definition 2.3.3: the integrated (average)
risk decomposes as an integral of the posterior expected loss over the predictive distribution,
$$r(\pi, \delta) = \int_{\mathcal X} \Big(\int_\Theta \ell(\theta, \delta(x))\,\pi(d\theta\mid x)\Big)\,m(dx),$$
so an estimator that minimizes the posterior expected loss pointwise (for predictive-a.e. `x`) is
a Bayes estimator.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §2.3, Theorem 2.3.2
and eq. (2.3.1) (integrated risk = integrated posterior expected loss), Definition 2.3.3 (Bayes
estimator), p. 62–63.

**Proof formalization notes.** This is proved *from the textbook* using only pinned Mathlib
primitives; it is not adapted from any external Lean development. The engine is the disintegration
`(P ∘ₘ π) ⊗ₘ (P†π) = (π ⊗ₘ P).map Prod.swap` (Mathlib's `compProd_posterior_eq_map_swap`), which is
exactly Robert's Fubini step (2.3.1):
`avgRisk ℓ P (deterministic δ) π = ∫⁻ (θ,x), ℓ θ (δ x) ∂(π ⊗ₘ P)` (by
`Measure.lintegral_compProd` and `Kernel.lintegral_deterministic'`), then pushed through
`Prod.swap` via `lintegral_map` to `∫⁻ x, ∫⁻ θ, ℓ θ (δ x) ∂(P†π) x ∂(P ∘ₘ π)`. The Bayes-risk
lower bound uses `iInf_le_lintegral` (needs `IsProbabilityMeasure ((P†π) x)`, from the posterior's
Markov instance); `isBayesEstimator_of_ae_argmin` closes by the `bayesRisk_le_avgRisk` sandwich.
No copied code; `IsBayesEstimator` is our own definition (`Decision.Defs`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨}

/-- **Robert Theorem 2.3.2 / eq. (2.3.1)** for a deterministic estimator `δ`: the integrated risk
equals the integral over the data of the posterior expected loss. -/
theorem avgRisk_deterministic_eq_lintegral_posteriorRisk [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    -- LEAN-ONLY: joint measurability of the loss (regularity)
    (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    -- LEAN-ONLY: the estimator `δ` is measurable (regularity of a free-choice input)
    {δ : 𝓧 → 𝓨} (hδ : Measurable δ) :
    avgRisk ℓ P (Kernel.deterministic δ hδ) π
      = ∫⁻ x, (∫⁻ θ, ℓ θ (δ x) ∂(P†π) x) ∂(P ∘ₘ π) := sorry

/-- The Bayes risk is bounded below by the integral of the pointwise-minimal posterior expected
loss (Robert Theorem 2.3.2, the "≥" half). -/
theorem lintegral_iInf_posteriorRisk_le_bayesRisk [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    -- LEAN-ONLY: joint measurability of the loss
    (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    (∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π)) ≤ bayesRisk ℓ P π := sorry

/-- **Robert Theorem 2.3.2**: a deterministic estimator that minimizes the posterior expected loss
pointwise, for predictive-a.e. `x`, is a Bayes estimator. -/
theorem isBayesEstimator_of_ae_argmin [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    -- LEAN-ONLY: joint measurability of the loss
    (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    -- LEAN-ONLY: the estimator `δ` is measurable
    {δ : 𝓧 → 𝓨} (hδ : Measurable δ)
    -- USER-INPUT: `δ(x)` minimizes the posterior expected loss for predictive-a.e. `x`;
    -- Robert Theorem 2.3.2
    (hmin : ∀ᵐ x ∂(P ∘ₘ π), ∀ y, ∫⁻ θ, ℓ θ (δ x) ∂(P†π) x ≤ ∫⁻ θ, ℓ θ y ∂(P†π) x) :
    IsBayesEstimator ℓ P (Kernel.deterministic δ hδ) π := sorry

end StatLean.Bayesian
