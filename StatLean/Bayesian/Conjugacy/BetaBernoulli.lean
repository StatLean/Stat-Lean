import StatLean.Bayesian.Conjugacy.BetaBinomial
import StatLean.Bayesian.ForMathlib.IIDKernel
import StatLean.Bayesian.Updating.Defs

/-!
# Beta-Bernoulli conjugacy and Laplace's rule of succession

For iid Bernoulli data with a Beta prior on the success probability:

* **posterior**: after `n` tosses with `s = successes y`,
  `θ | y ~ Beta(α + s, β + (n − s))`;
* **posterior mean of the success probability** (`lintegral_unitClamp_betaMeasure`):
  `E[θ] = α/(α + β)` under `Beta(α, β)`;
* **Laplace's rule of succession** (Robert §1.2's historical example, formalized via the posterior
  predictive): the predictive probability of a further success is
  $$P(y_{n+1} = 1 \mid y_{1:n}) = \frac{\alpha + s}{\alpha + \beta + n}.$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Example 1.4.1 (Beta-Binomial machinery), pp. 22–23; Table 4.2.1
(posterior mean `(α+x)/(α+β+n)`), p. 176; the succession rule is Laplace's 1774 computation,
recounted by Robert in §1.8.1.

**Proof formalization notes.** The iid Bernoulli likelihood is a clamped-power factor with
exponents `successes y` and `n − successes y` (`Bool.toNat` bookkeeping), so the posterior is the
Beta-Binomial algebra (`betaPDF_mul_clampPow`) fed to the criterion via `iidKernel_withDensity`.
The succession rule composes the posterior with one more Bernoulli through `posteriorPredictive`
and evaluates `{true}` by the Beta-mean lemma, itself proved by the pdf-ratio trick
(`betaPDF_mul_clampPow` with exponents `(1, 0)` + `lintegral_betaPDF_eq_one` + `Real.Gamma_add_one`
for the Beta-function ratio `B(α+1,β)/B(α,β) = α/(α+β)`).

**Bibliographic comments.** The rule of succession is P. S. Laplace's ("Mémoire sur la
probabilité des causes par les événements," 1774): after the sun has risen `n` times, the odds it
rises again are `(n+1)/(n+2)` — the case `α = β = 1`, `s = n`. It is the first posterior
predictive computation in history and the standard smoothing device ("add-one" or Laplace
smoothing) in modern categorical modeling. Robert §1.8.1 surveys the history; de Finetti's
representation theorem (Robert §3.8.2) explains why exchangeable binary data reduce to exactly
this model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- The Bernoulli kernel is Markov for every real parameter (clamping). -/
instance : IsMarkovKernel bernoulliKernel := sorry

/-- **Posterior mean of a clamped success probability under a Beta law**: `α/(α+β)` (Robert
Table 4.2.1 row 4 with `n = 1`, `x = 1`; the pdf-ratio trick). -/
theorem lintegral_unitClamp_betaMeasure {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Robert Appendix A.3
    (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ θ, ENNReal.ofReal (unitClamp θ) ∂betaMeasure α β
      = ENNReal.ofReal (α / (α + β)) := sorry

/-- **Beta-Bernoulli posterior** (iid sample): `θ | y ~ Beta(α + s, β + (n − s))` with
`s = successes y`, predictive-a.e. -/
theorem beta_bernoulli_posterior_ae {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Robert Appendix A.3
    (hα : 0 < α) (hβ : 0 < β)
    -- LEAN-ONLY: instance plumbing, derivable from hα/hβ via `isProbabilityMeasureBeta`
    [IsFiniteMeasure (betaMeasure α β)] (n : ℕ) :
    ∀ᵐ y ∂(iidKernel bernoulliKernel n ∘ₘ betaMeasure α β),
      ((iidKernel bernoulliKernel n)†(betaMeasure α β)) y
        = betaMeasure (α + successes y) (β + ((n - successes y : ℕ) : ℝ)) := sorry

/-- **Laplace's rule of succession** (Robert §1.8.1; Table 4.2.1): the posterior predictive
probability of one more success after `n` tosses with `s` successes is `(α + s)/(α + β + n)`,
predictive-a.e. -/
theorem beta_bernoulli_posteriorPredictive_true_ae {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Robert Appendix A.3
    (hα : 0 < α) (hβ : 0 < β)
    -- LEAN-ONLY: instance plumbing, derivable from hα/hβ via `isProbabilityMeasureBeta`
    [IsFiniteMeasure (betaMeasure α β)] (n : ℕ) :
    ∀ᵐ y ∂(iidKernel bernoulliKernel n ∘ₘ betaMeasure α β),
      posteriorPredictive (iidKernel bernoulliKernel n) bernoulliKernel (betaMeasure α β) y {true}
        = ENNReal.ofReal ((α + successes y) / (α + β + n)) := sorry

end StatLean.Bayesian
