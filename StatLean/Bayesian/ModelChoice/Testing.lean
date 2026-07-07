import StatLean.Bayesian.ModelChoice.Defs
import StatLean.Bayesian.Decision.BayesEstimator
import StatLean.Bayesian.Dominated.PosteriorDensity

/-!
# Bayesian testing: the threshold rule and point-null mixtures

Two testing results:

* **the Bayes test under asymmetric 0–1 loss** (Robert Proposition 5.2.2): the rule accepting
  `H₀ : θ ∈ Θ₀` iff `a₁·π(Θ₀ᶜ|x) ≤ a₀·π(Θ₀|x)` — equivalently iff
  `π(Θ₀|x) ≥ a₁/(a₀+a₁)` — is a Bayes estimator for the `a₀–a₁` loss;
* **the point-null posterior probability** (Robert §5.2.4): under the mixture prior
  `w·δ_{θ₀} + (1−w)·π₁`,
  $$\pi(\{\theta_0\} \mid x)
    = \frac{w\,p(\theta_0, x)}{w\,p(\theta_0, x) + (1-w)\int p(\theta, x)\,\pi_1(d\theta)}
    \qquad \text{predictive-a.e.}$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §5.2.1, eq. (5.2.1) and Proposition 5.2.2, p. 225; eq. (5.2.3),
p. 227; §5.2.3 (the mixture prior, Dirac at `θ₀`), p. 229; §5.2.4 (the posterior-probability
formula, verbatim but unnumbered), p. 231.

**Proof formalization notes.** The test: posterior expected losses of the two actions are
`a₁·post(Θ₀ᶜ)` and `a₀·post(Θ₀)` (indicator lintegrals of `hypLoss`), so the a.e.-argmin engine
`isBayesEstimator_of_ae_argmin` (Batch 1) applies with a `Bool.rec` over actions; measurability of
`bayesTest` comes from `Kernel.measurable_coe`. The point-null formula: the mixture prior is
finite by instances (`w : ℝ≥0` smul), the predictive density over it splits by
`lintegral_add_measure`/`lintegral_smul_measure`/`lintegral_dirac'`, and the posterior singleton
mass follows from the Batch-1 headline with `withDensity_apply` on `{θ₀}` (the hypothesis
`π₁{θ₀} = 0` keeps the alternative from contaminating the atom).

**Bibliographic comments.** The threshold structure of Bayes tests is the Bayesian counterpart of
the Neyman–Pearson lemma (1933) and appears with the a₀–a₁ loss in Robert §5.2 following Wald's
decision theory. Point-null mixture priors originate with H. Jeffreys (1939) and were sharpened
into calibration results by J. O. Berger and T. Sellke ("Testing a point null hypothesis: the
irreconcilability of P values and evidence," *J. Amer. Statist. Assoc.* 82 (1987), 112–122),
Robert's §5.2.4 companion reading.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- The Bayes test is a measurable decision rule. -/
theorem measurable_bayesTest [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    {Θ₀ : Set Θ}
    -- LEAN-ONLY: the null hypothesis is an event (regularity)
    (hΘ₀ : MeasurableSet Θ₀) (a₀ a₁ : ℝ≥0∞) :
    Measurable (bayesTest κ π Θ₀ a₀ a₁) := sorry

/-- **The Bayes test is a Bayes estimator for the `a₀–a₁` loss** (Robert Proposition 5.2.2). -/
theorem isBayesEstimator_bayesTest [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    {Θ₀ : Set Θ}
    -- LEAN-ONLY: the null hypothesis is an event (regularity)
    (hΘ₀ : MeasurableSet Θ₀) (a₀ a₁ : ℝ≥0∞) :
    IsBayesEstimator (hypLoss Θ₀ a₀ a₁) κ
      (Kernel.deterministic (bayesTest κ π Θ₀ a₀ a₁) (measurable_bayesTest κ π hΘ₀ a₀ a₁))
      π := sorry

/-- **Threshold form of the Bayes test** (Robert Proposition 5.2.2 / eq. (5.2.3)): for
nondegenerate `a₀ + a₁`, the test accepts iff the posterior null probability is at least
`a₁/(a₀+a₁)`. -/
theorem bayesTest_eq_threshold [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    {Θ₀ : Set Θ}
    -- LEAN-ONLY: the null hypothesis is an event (regularity)
    (hΘ₀ : MeasurableSet Θ₀) {a₀ a₁ : ℝ≥0∞}
    -- USER-INPUT: nondegenerate loss weights; Robert eq. (5.2.1)
    (h0 : a₀ + a₁ ≠ 0) (h1 : a₀ + a₁ ≠ ∞) (x : 𝓧) :
    bayesTest κ π Θ₀ a₀ a₁ x = (a₁ / (a₀ + a₁) ≤ (κ†π) x Θ₀ : Bool) := sorry

/-- **Point-null posterior probability** (Robert §5.2.4, p. 231): under the mixture prior
`w·δ_{θ₀} + (1−w)·π₁` with `π₁{θ₀} = 0`, the posterior mass of the null atom is
`w·p(θ₀,x) / (w·p(θ₀,x) + (1−w)·m₁(x))`, predictive-a.e. -/
theorem pointNull_posterior_singleton_ae [StandardBorelSpace Θ] [Nonempty Θ]
    [MeasurableSingletonClass Θ]
    {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    {w : ℝ≥0}
    -- USER-INPUT: the null prior weight is a probability; Robert §5.2.3
    (hw : w ≤ 1) {θ₀ : Θ} {π₁ : Measure Θ} [IsProbabilityMeasure π₁]
    -- USER-INPUT: the alternative prior puts no mass at the null point; Robert §5.2.3
    (hπ₁ : π₁ {θ₀} = 0) :
    ∀ᵐ x ∂(κ ∘ₘ (w • Measure.dirac θ₀ + (1 - w) • π₁)),
      (κ†(w • Measure.dirac θ₀ + (1 - w) • π₁)) x {θ₀}
        = (w : ℝ≥0∞) * p θ₀ x
            / ((w : ℝ≥0∞) * p θ₀ x + ((1 - w : ℝ≥0) : ℝ≥0∞) * ∫⁻ θ, p θ x ∂π₁) := sorry

end StatLean.Bayesian
