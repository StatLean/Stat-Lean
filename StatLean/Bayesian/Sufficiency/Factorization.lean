import StatLean.Bayesian.Sufficiency.Defs
import StatLean.Bayesian.GeneralizedBayes.Defs
import StatLean.Bayesian.Dominated.PosteriorDensity

/-!
# Factorized likelihoods: posterior reduction and the likelihood principle

Consequences of the Fisher–Neyman factorization `p(θ, x) = g(θ, T x) · h(x)` for a dominated
model:

* the base factor `h` **cancels from the posterior** — the posterior at `x` is the
  `g(·, T x)`-reweighted prior (Robert's "the factor h(x) disappears," §1.3.1);
* the **posterior depends on the data only through the sufficient statistic**:
  `(κ†π) x = ((statKernel κ T)†π) (T x)` for predictive-a.e. `x`;
* the **likelihood principle**, dominated version: proportional likelihoods (`p₁(·, x₁) =
  c · p₂(·, x₂)`) give equal posteriors under the same prior (Robert §1.3.2).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.3.1 (Definition 1.3.1 and the factorization theorem, p. 14);
§1.3.2 (the Likelihood Principle, stated as a boldface display, pp. 15–16, and the observation on
p. 16 that the posterior (1.2.3) depends on `x` only through the likelihood).

**Proof formalization notes.** The cancellation is `withDensity` algebra: at data with
`h(x) ∉ {0, ∞}` the ratio `p/m` equals `g/(∫ g dπ)` pointwise (`ENNReal.mul_div_mul_right`-style).
For the statistic reduction, the key bridge is `map_withDensity_comp` (a density factoring through
`T` passes through `Measure.map T`), which exhibits the statistic experiment as dominated by
`(ν.withDensity h).map T` with density `g`; both experiments' posteriors are then identified by the
Batch-1 dominated Bayes theorem, and the exceptional sets transport because `h ∈ (0, ∞)` holds
`(κ ∘ₘ π)`-a.e. (forced by `predictiveDensity_pos_ae`/`_lt_top_ae_comp` — not hypotheses). The
likelihood principle is the scalar case of the same cancellation.

**Bibliographic comments.** The Likelihood Principle was articulated by G. Barnard (1949) and
R. A. Fisher, given its modern form by A. Birnbaum ("On the foundations of statistical inference,"
*J. Amer. Statist. Assoc.* 57 (1962), 269–306 — Robert's Theorem 1.3.8: sufficiency +
conditionality ⇔ likelihood), and defended at book length by J. O. Berger and R. L. Wolpert,
*The Likelihood Principle* (IMS, 1988). That Bayesian inference automatically obeys it (the
posterior depends only on the likelihood) is Robert's observation on p. 16, formalized here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 S : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [mS : MeasurableSpace S]

/-- The statistic kernel is the pushforward: `statKernel K T hT θ = (K θ).map T`
(Robert §1.3.1). -/
theorem statKernel_apply (K : Kernel Θ 𝓧) {T : 𝓧 → S} (hT : Measurable T) (θ : Θ) :
    statKernel K hT θ = (K θ).map T := sorry

/-- A density factoring through `T` passes through the pushforward:
`(μ.withDensity (f ∘ T)).map T = (μ.map T).withDensity f`. -/
theorem map_withDensity_comp {T : 𝓧 → S}
    -- LEAN-ONLY: the statistic and the density are measurable (regularity)
    (hT : Measurable T) {f : S → ℝ≥0∞} (hf : Measurable f) (μ : Measure 𝓧) :
    (μ.withDensity fun x => f (T x)).map T = (μ.map T).withDensity f := sorry

/-- **The base factor cancels from the posterior** (Robert §1.3.1): under a Fisher–Neyman
factorization, at any data point where `h(x) ∉ {0, ∞}` the generalized posterior is the
`g(·, T x)`-reweighted prior. -/
theorem generalizedPosterior_of_factorized {p : Θ → 𝓧 → ℝ≥0∞} {T : 𝓧 → S}
    {g : Θ → S → ℝ≥0∞} {h : 𝓧 → ℝ≥0∞} {π : Measure Θ}
    -- USER-INPUT: Fisher–Neyman factorization of the likelihood; Robert §1.3.1, p. 14
    (hfac : IsFactorizedLikelihood p T g h) {x : 𝓧}
    -- USER-INPUT: the base factor is positive and finite at the observed data; Robert §1.3.1
    (hx0 : h x ≠ 0) (hx' : h x ≠ ∞) :
    generalizedPosterior p π x
      = π.withDensity fun θ => g θ (T x) / ∫⁻ θ', g θ' (T x) ∂π := sorry

/-- **The posterior depends on the data only through a sufficient statistic** (Robert §1.3.1–1.3.2,
dominated form): under a Fisher–Neyman factorization, the full-data posterior at `x` equals the
statistic-experiment posterior at `T x`, for predictive-almost-every `x`. -/
theorem posterior_ae_eq_posterior_statKernel [StandardBorelSpace Θ] [Nonempty Θ]
    {π : Measure Θ} [IsFiniteMeasure π] {κ : Kernel Θ 𝓧} [IsFiniteKernel κ]
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞} {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the density family, statistic, and factors (regularity)
    (hp : Measurable (Function.uncurry p)) (hT : Measurable T)
    {g : Θ → S → ℝ≥0∞} (hg : Measurable (Function.uncurry g))
    {h : 𝓧 → ℝ≥0∞} (hh : Measurable h)
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    -- USER-INPUT: Fisher–Neyman factorization of the likelihood; Robert §1.3.1, p. 14
    (hfac : IsFactorizedLikelihood p T g h) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x = ((statKernel κ hT)†π) (T x) := sorry

/-- **The likelihood principle**, dominated version (Robert §1.3.2, pp. 15–16): proportional
likelihoods yield the same posterior under the same prior. -/
theorem generalizedPosterior_eq_of_likelihood_proportional {p₁ p₂ : Θ → 𝓧 → ℝ≥0∞}
    {π : Measure Θ} {x₁ x₂ : 𝓧} {c : ℝ≥0∞}
    -- USER-INPUT: the proportionality constant is nondegenerate; Robert §1.3.2
    (hc0 : c ≠ 0) (hc' : c ≠ ∞)
    -- USER-INPUT: the two observations have proportional likelihoods; Robert §1.3.2
    (hprop : ∀ θ, p₁ θ x₁ = c * p₂ θ x₂) :
    generalizedPosterior p₁ π x₁ = generalizedPosterior p₂ π x₂ := sorry

end StatLean.Bayesian
