import StatLean.Bayesian.ForMathlib.IIDKernel
import StatLean.Bayesian.Dominated.PosteriorDensity

/-!
# The iid posterior (product likelihood)

Bayes' theorem for an iid sample: for `x = (x₁, …, xₙ)` drawn iid from the dominated model
`κ θ = ν.withDensity (p θ)`, the posterior is the prior reweighted by the **product likelihood**,
$$\pi(d\theta \mid x_{1:n})
  = \frac{\prod_{i=1}^n p(\theta, x_i)\,\pi(d\theta)}
         {\int_\Theta \prod_{i=1}^n p(\theta', x_i)\,\pi(d\theta')}
  \qquad \text{for predictive-a.e. } x_{1:n}.$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.3, p. 13 (iid samples and the product likelihood); §1.4 (the
posterior machine applied to a sample); sequential coherence is eq. (1.4.1), p. 23.

**Proof formalization notes.** A one-shot application of the Batch-1 dominated Bayes theorem
(`posterior_eq_withDensity_likelihood_div_predictive`) to `iidKernel κ n`, whose domination with
the product density is `iidKernel_withDensity` and whose density's joint measurability is
`measurable_uncurry_prod_likelihood`; the dominating measure is `Measure.pi (fun _ => ν)`
(σ-finite, hence `SFinite`).

**Bibliographic comments.** Posterior updating on an iid sample is the original setting of both
Bayes (1763, binomial counts) and Laplace (1774); the product-likelihood form is implicit in every
conjugate analysis of Robert §3.3/§4.2, where "when several observations are available … only the
parameters in the estimator are modified by virtue of the sufficiency properties" (Robert §4.2.2,
p. 175). The `n`-observation exponential-family update is `Conjugacy.ExpFamily`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **The iid posterior** (Robert §1.3–§1.4): for a dominated model and an iid sample of size `n`,
the posterior is the prior reweighted by the normalized product likelihood, predictive-a.e. -/
theorem posterior_iid_eq_withDensity_prod_likelihood
    [StandardBorelSpace Θ] [Nonempty Θ] {π : Measure Θ} [IsFiniteMeasure π]
    {κ : Kernel Θ 𝓧} [IsMarkovKernel κ] {ν : Measure 𝓧} [SigmaFinite ν]
    {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model, K(θ, ·) = p(θ, ·) ν; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) (n : ℕ) :
    ∀ᵐ x ∂(iidKernel κ n ∘ₘ π),
      ((iidKernel κ n)†π) x
        = π.withDensity fun θ => (∏ i, p θ (x i)) / ∫⁻ θ', ∏ i, p θ' (x i) ∂π :=
  posterior_eq_withDensity_likelihood_div_predictive
    (ν := Measure.pi fun _ => ν)
    (measurable_uncurry_prod_likelihood hp) (iidKernel_withDensity hp hκ n)

end StatLean.Bayesian
