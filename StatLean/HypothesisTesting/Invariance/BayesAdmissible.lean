import StatLean.HypothesisTesting.Invariance.Admissibility
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Admissibility via unique Bayes solutions, and the Gaussian scale-mixture device

A general decision-theoretic route to admissibility is to exhibit a procedure as the
**unique Bayes solution** of some prior problem. For testing, the prior problem is a pair
of priors — one carried by the null class, one by the alternative class — under 0–1 loss.
Averaging the two families produces two mixture densities
$$ h_i(x) \;=\; \int f_\theta(x)\,d\Lambda_i(\theta), \qquad i = 0, 1, $$
and the Bayes test rejects where `h₁ ≥ k h₀`. This is a Neyman–Pearson test for the simple
problem `h₀` versus `h₁`; when the boundary `{h₁ = k h₀}` is null, that test is unique, and
uniqueness upgrades directly to admissibility of the original test. If moreover the prior
on the null class concentrates on the parameters where the size `α` is attained, the
sharper `α`-admissibility follows. Everything applies verbatim to any subclass of
alternatives carrying the alternative prior.

The second half of the file records the device that makes the method work in normal
problems with **nuisance means**. A Gaussian location family with a fixed variance `σ²`,
mixed over its mean by a suitable prior, reproduces a centred Gaussian of any larger
variance `M²`; choosing `M²` above all the variances in play makes the contribution of the
nuisance means to the likelihood ratio cancel, so that the ratio reduces to the one
computed with the means known.

**Main results.**
* `mixtureDensity`, `bayesTest` — the two-prior mixture densities and the nonrandomized
  Bayes test;
* `bayesTest_isDAdmissible`, `bayesTest_isAlphaAdmissible` — admissibility of the Bayes
  test against the alternative class;
* `bayesTest_admissible_of_subset` — the same conclusions against any subclass carrying
  the alternative prior;
* `exists_gaussian_scale_mixture` — the mixing identity producing a centred Gaussian of
  prescribed larger variance.

**Proof formalization notes.**
* The boundary condition is written division-free as `μ {x | h₁ x = k * h₀ x} = 0`; with
  the `θ`-free support hypothesis this is the same as the vanishing of the set where the
  likelihood ratio equals `k`, and it avoids junk values of division.
* The support hypothesis (`hsupp`) is the source's "the set `{x : f_θ(x) > 0}` does not
  depend on `θ`"; the joint measurability of `(θ, x) ↦ f_θ(x)` is what makes the mixture
  densities measurable.
* The priors are probability measures on the parameter space with `Λ₀` carried by the null
  class and `Λ₁` by the alternative class, transcribing `Λ₀(Θ_H) = Λ₁(Θ_K) = 1`.
* `bayesTest` is nonrandomized by construction, matching the source: randomized
  competitors are allowed, but the Bayes test itself must be an indicator for the
  uniqueness argument to apply.
* `exists_gaussian_scale_mixture` is stated in two equivalent readings: the pointwise
  density identity of the source, and the measure-level mixture identity. The intended
  tool for the construction (the mixing prior is itself centred Gaussian, of variance
  `M² − σ²`) is the normal–normal conjugacy already developed in `StatLean.Bayesian`.
* Positivity `σ² ≠ 0` is required for the Gaussian density to be the nondegenerate one;
  the source's `σ²` is a genuine variance.

**Bibliographic comments.** Exhibiting a test as a unique Bayes solution as a route to
admissibility, and the limiting-prior technique behind the normal examples, are due to
C. Stein ("The admissibility of Hotelling's $T^2$-test," *Ann. Math. Statist.* **27**
(1956), 616–623) and A. Birnbaum ("Characterizations of complete classes of tests of some
multiparametric hypotheses, with applications to likelihood ratio tests," *Ann. Math.
Statist.* **26** (1955), 21–36); the corresponding complete-class results for the
multivariate exponential family are due to K. Matthes and D. R. Truax ("Tests of composite
hypotheses for the multivariate exponential family," *Ann. Math. Statist.* **38** (1967),
681–697). The admissibility of the one- and two-sided $t$-tests against all invariant
classes of alternatives, obtained by approximating the improper uniform prior on
$\log\sigma$, is due to E. L. Lehmann and C. Stein (1953), extending their earlier joint
work (*Ann. Math. Statist.* **20** (1949), 28–45). The underlying optimality criterion is
that of J. Neyman and E. S. Pearson (*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

/-! ## The two-prior Bayes test -/

section Bayes

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Θ]

/-- The **mixture density** of a dominated family against a prior:
`h(x) = ∫ f_θ(x) dΛ(θ)`. -/
noncomputable def mixtureDensity (f : Θ → 𝓧 → ℝ) (Λ : Measure Θ) (x : 𝓧) : ℝ :=
  ∫ θ, f θ x ∂Λ

/-- The **nonrandomized Bayes test** for the two-prior 0–1-loss problem with threshold
`k`: reject exactly where the alternative mixture density is at least `k` times the null
mixture density. -/
noncomputable def bayesTest (h₀ h₁ : 𝓧 → ℝ) (k : ℝ) : 𝓧 → ℝ :=
  fun x => if k * h₀ x ≤ h₁ x then 1 else 0

/-- **A Bayes test with null boundary is d-admissible.** -/
theorem bayesTest_isDAdmissible {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K : Set Θ} {k : ℝ}
    -- USER-INPUT: the model is dominated by `μ` with densities `f`, jointly measurable
    -- in parameter and observation
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the null and alternative classes are measurable
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K)
    -- USER-INPUT: the priors are carried by the null and alternative classes
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ_K = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0) :
    IsDAdmissible P Θ_H Θ_K
      (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  sorry

/-- **A Bayes test whose null prior concentrates on the size-attaining parameters is
`α`-admissible.** -/
theorem bayesTest_isAlphaAdmissible {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K : Set Θ} {k α : ℝ}
    -- USER-INPUT: dominated model with jointly measurable nonnegative densities
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the null and alternative classes are measurable
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K)
    -- USER-INPUT: the priors are carried by the null and alternative classes
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ_K = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    -- USER-INPUT: `α` is the size of the Bayes test on the null class
    (hlevel : IsLevel P Θ_H (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) α)
    -- USER-INPUT: the null prior concentrates on the parameters where the size is attained
    (hω : Λ₀ {θ ∈ Θ_H |
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ = α} = 1) :
    IsAlphaAdmissible P Θ_H Θ_K α
      (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  sorry

/-- **Admissibility against any subclass carrying the alternative prior.** If `Λ₁` gives
probability one to a subclass `Θ'` of the alternatives, both conclusions hold with `Θ'` in
place of the full alternative class. -/
theorem bayesTest_admissible_of_subset {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K Θ' : Set Θ} {k α : ℝ}
    -- USER-INPUT: dominated model with jointly measurable nonnegative densities
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the classes are measurable and `Θ'` is a subclass of the alternatives
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K) (hΘ' : MeasurableSet Θ')
    (hsub : Θ' ⊆ Θ_K)
    -- USER-INPUT: the priors are carried by the null class and by the subclass
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ' = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    -- USER-INPUT: `α` is the size of the Bayes test, attained `Λ₀`-almost surely
    (hlevel : IsLevel P Θ_H (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) α)
    (hω : Λ₀ {θ ∈ Θ_H |
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ = α} = 1) :
    IsDAdmissible P Θ_H Θ'
        (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) ∧
      IsAlphaAdmissible P Θ_H Θ' α
        (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  sorry

end Bayes

/-! ## The Gaussian scale-mixture identity -/

/-- **Mixing a Gaussian location family over its mean reproduces a wider centred
Gaussian.** For a variance `σ² > 0` and any larger `M²`, there is a prior on the mean
under which the mixture of `N(ζ, σ²)` over `ζ` is exactly `N(0, M²)` — stated both as the
pointwise density identity and as the measure-level mixture identity.

This is the device that removes nuisance means from a likelihood ratio: choosing `M²`
above every variance in play makes the mean contributions to the two mixture densities
cancel. The intended construction takes the mixing prior itself centred Gaussian with
variance `M² − σ²`, for which the normal–normal conjugacy of `StatLean.Bayesian` supplies
the computation. -/
theorem exists_gaussian_scale_mixture {σ2 M2 : NNReal}
    -- USER-INPUT: the inner variance is nondegenerate
    (hσ : σ2 ≠ 0)
    -- USER-INPUT: the target variance is strictly larger
    (hσM : σ2 < M2) :
    ∃ Λ : Measure ℝ, IsProbabilityMeasure Λ ∧
      (∀ z : ℝ, ∫ ζ, gaussianPDFReal ζ σ2 z ∂Λ = gaussianPDFReal 0 M2 z) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        ∫⁻ ζ, gaussianReal ζ σ2 B ∂Λ = gaussianReal 0 M2 B) := by
  sorry

end StatLean.HypothesisTesting
