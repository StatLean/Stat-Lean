import StatLean.Bayesian.Conjugacy.Defs
import StatLean.Bayesian.Conjugacy.Criterion
import Mathlib.Probability.Distributions.Beta

/-!
# Beta-Binomial conjugacy

The classical first example of Bayes' theorem: for a success probability `θ ~ Beta(α, β)` and one
binomial observation `k ~ ℬ(n, θ)`,

* **posterior** (Robert Example 1.4.1 / Table 3.3.1): `θ | k ~ Beta(α + k, β + n − k)`;
* **marginal** (the Beta-Binomial pmf, Robert Example 1.4.1):
  `P(k) = C(n, k) · B(α + k, β + n − k) / B(α, β)`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Example 1.4.1 (the worked Beta-Binomial update, incl. the
Γ-function marginal), pp. 22–23; Table 3.3.1 (Binomial ℬ(n,θ) + Beta ℬe(α,β) → ℬe(α+x, β+n−x)),
p. 121; Appendix A.3/A.10, pp. 519–521.

**Proof formalization notes.** One pointwise pdf-algebra lemma (`betaPDF_mul_clampPow`: Beta pdf ×
clamped power = Beta-function ratio × updated Beta pdf, using `Real.rpow_natCast`/`rpow_add` on
`(0,1)` where the clamp is the identity, and `ProbabilityTheory.beta` in Γ-form) feeds the
conjugacy criterion; the data space `Fin (n+1)` is finite discrete, and the binomial kernel's
Markov property is the binomial theorem `add_pow` at `clamp θ + (1 − clamp θ) = 1`. Off `(0, 1)`
both sides of the algebra vanish (the Beta pdf is zero), which is why clamping is harmless.

**Bibliographic comments.** This is the original Bayesian computation: Bayes's 1763 essay treats
exactly the uniform-prior case `Beta(1,1)` (as Robert recounts in §1.2), and Laplace's rule of
succession builds on it (`Conjugacy.BetaBernoulli`). The modern conjugate-family reading is
Raiffa–Schlaifer (1961); Diaconis and Ylvisaker (1985, "Quantifying prior opinion") use the
spinning-coin Beta-Binomial as the canonical worked example (Robert Example 3.4.1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- The binomial kernel is Markov for every real parameter (clamping; binomial theorem). -/
instance (n : ℕ) : IsMarkovKernel (binomialKernel n) := sorry

/-- Pointwise pdf algebra: Beta pdf times a clamped-power factor is a Beta-function ratio times
the updated Beta pdf. Both sides vanish off `(0, 1)`. -/
theorem betaPDF_mul_clampPow {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Robert Appendix A.3
    (hα : 0 < α) (hβ : 0 < β) (a b : ℕ) (θ : ℝ) :
    betaPDF α β θ * ENNReal.ofReal (unitClamp θ ^ a * (1 - unitClamp θ) ^ b)
      = ENNReal.ofReal (ProbabilityTheory.beta (α + a) (β + b) / ProbabilityTheory.beta α β)
          * betaPDF (α + a) (β + b) θ := sorry

/-- **Beta-Binomial posterior** (Robert Example 1.4.1 / Table 3.3.1): observing `k` successes in
`n` trials updates `Beta(α, β)` to `Beta(α + k, β + (n − k))`, predictive-a.e. -/
theorem beta_binomial_posterior_ae {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Robert Appendix A.3
    (hα : 0 < α) (hβ : 0 < β)
    -- LEAN-ONLY: instance plumbing, derivable from hα/hβ via `isProbabilityMeasureBeta`
    [IsFiniteMeasure (betaMeasure α β)] (n : ℕ) :
    ∀ᵐ k ∂(binomialKernel n ∘ₘ betaMeasure α β),
      ((binomialKernel n)†(betaMeasure α β)) k
        = betaMeasure (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) := sorry

/-- **Beta-Binomial marginal** (Robert Example 1.4.1): the prior predictive pmf is
`C(n,k) · B(α+k, β+n−k) / B(α, β)`. -/
theorem beta_binomial_predictiveDensity {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Robert Appendix A.3
    (hα : 0 < α) (hβ : 0 < β) (n : ℕ) (k : Fin (n + 1)) :
    predictiveDensity (binomialDensity n) (betaMeasure α β) k
      = ENNReal.ofReal ((n.choose k : ℝ)
          * ProbabilityTheory.beta (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ))
          / ProbabilityTheory.beta α β) := sorry

end StatLean.Bayesian
