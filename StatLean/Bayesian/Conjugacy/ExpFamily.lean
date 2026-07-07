import StatLean.Bayesian.Conjugacy.Defs
import StatLean.Bayesian.Conjugacy.Criterion
import StatLean.Bayesian.ForMathlib.IIDKernel

/-!
# Exponential-family conjugacy (Diaconis–Ylvisaker)

The single most reusable conjugacy theorem: for a natural exponential family
`p(θ, x) = h(x)·exp(⟨η θ, T x⟩ − A θ)` with Diaconis–Ylvisaker conjugate prior
`π_{χ,ν₀} ∝ exp(⟨χ, η θ⟩ − ν₀ A θ) μ₀(dθ)`,

* **conjugate update** (Robert Prop. 3.3.13): after `n` iid observations `x₁, …, xₙ`,
  $$\pi_{\chi,\nu_0}(\cdot \mid x_{1:n}) = \pi_{\chi + \sum_i T(x_i),\ \nu_0 + n},$$
* **marginal as normalizer ratio**: the predictive density is
  $$m(x_{1:n}) = \Big(\prod_i h(x_i)\Big)\,
    \frac{Z(\chi + \sum_i T(x_i),\ \nu_0 + n)}{Z(\chi, \nu_0)}.$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §3.3.3, Proposition 3.3.13 and eqs. (3.3.4)–(3.3.5), p. 120
(single observation); the `n`-sample form via sufficiency, §4.2.2, p. 175 and eq. (3.3.6).

**Proof formalization notes.** The pointwise weight algebra is
`conjExpWeight χ ν₀ θ · ∏ᵢ p(θ, xᵢ) = (∏ᵢ h xᵢ) · conjExpWeight (χ + ∑ᵢ T xᵢ) (ν₀ + n) θ`
(`Real.exp_add`, sum rearrangement, `ENNReal.ofReal_mul`), fed to the conjugacy criterion with
the iid product density (`iidKernel_withDensity`). Propriety of the prior and of every updated
prior (`0 < Z < ∞`) is Robert's condition (3.3.5) — a genuine USER-INPUT (Diaconis–Ylvisaker give
`ν₀ > 0`, `χ/ν₀` interior as sufficient conditions; we take the propriety itself as hypothesis to
stay measure-theoretically minimal). The base factor must be finite (`h x ≠ ∞`) for the scalar
manipulations; base densities are finite in every model.

**Bibliographic comments.** The conjugate family for a natural exponential family and the
posterior linearity that characterizes it are P. Diaconis and D. Ylvisaker, "Conjugate priors for
exponential families," *Ann. Statist.* 7 (1979), 269–281 (Robert Props. 3.3.13–3.3.14); the
conjugate-prior program itself is H. Raiffa and R. Schlaifer (1961). Exponential-family theory:
L. D. Brown (1986). In modern practice this theorem is the backbone of variational inference and
natural-gradient methods, where conjugate updates are the tractable primitives.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧] {d : ℕ}
  {η : Θ → Fin d → ℝ} {T : 𝓧 → Fin d → ℝ} {A : Θ → ℝ} {h : 𝓧 → ℝ≥0∞}
  {μ₀ : Measure Θ} {χ : Fin d → ℝ} {ν₀ : ℝ}

/-- Pointwise conjugate weight algebra: prior weight × product likelihood = base factors ×
updated weight. -/
theorem conjExpWeight_mul_prod_expFamilyDensity {n : ℕ}
    -- USER-INPUT: base factors are finite (true for every density model); Robert §3.3.3
    (hh' : ∀ x, h x ≠ ∞) (θ : Θ) (x : Fin n → 𝓧) :
    conjExpWeight η A χ ν₀ θ * ∏ i, expFamilyDensity η T A h θ (x i)
      = (∏ i, h (x i)) * conjExpWeight η A (χ + ∑ i, T (x i)) (ν₀ + n) θ := sorry

/-- The conjugate prior is a probability measure under propriety. -/
theorem isProbabilityMeasure_conjExpPrior
    -- USER-INPUT: prior propriety 0 < Z(χ, ν₀) < ∞; Robert eq. (3.3.5)
    (hZ0 : conjExpZ μ₀ η A χ ν₀ ≠ 0) (hZ' : conjExpZ μ₀ η A χ ν₀ ≠ ∞) :
    IsProbabilityMeasure (conjExpPrior μ₀ η A χ ν₀) := sorry

/-- **Exponential-family conjugate update, `n` iid observations** (Robert Proposition 3.3.13;
Table 4.2.1's sufficiency remark): the posterior of `π_{χ,ν₀}` after `x₁,…,xₙ` is
`π_{χ+∑T(xᵢ), ν₀+n}`, predictive-a.e. -/
theorem expFamily_iid_posterior_ae [StandardBorelSpace Θ] [Nonempty Θ]
    {ν : Measure 𝓧} [SigmaFinite ν] {κ : Kernel Θ 𝓧} [IsMarkovKernel κ]
    -- LEAN-ONLY: measurability of the family components (regularity)
    (hη : Measurable η) (hA : Measurable A) (hT : Measurable T) (hh : Measurable h)
    -- USER-INPUT: base factors are finite; Robert §3.3.3
    (hh' : ∀ x, h x ≠ ∞)
    -- USER-INPUT: the model is the dominated exponential family; Robert Def 3.3.2/eq. (3.3.1)
    (hκ : ∀ θ, κ θ = ν.withDensity (expFamilyDensity η T A h θ)) (n : ℕ)
    -- USER-INPUT: prior propriety 0 < Z(χ, ν₀) < ∞; Robert eq. (3.3.5)
    (hZ0 : conjExpZ μ₀ η A χ ν₀ ≠ 0) (hZ' : conjExpZ μ₀ η A χ ν₀ ≠ ∞)
    -- LEAN-ONLY: instance plumbing, derivable from hZ0/hZ' via `isProbabilityMeasure_conjExpPrior`
    [IsFiniteMeasure (conjExpPrior μ₀ η A χ ν₀)]
    -- USER-INPUT: propriety of every updated prior; Robert eq. (3.3.5)
    (hZn : ∀ x : Fin n → 𝓧,
      conjExpZ μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n) ≠ 0
        ∧ conjExpZ μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n) ≠ ∞) :
    ∀ᵐ x ∂(iidKernel κ n ∘ₘ conjExpPrior μ₀ η A χ ν₀),
      ((iidKernel κ n)†(conjExpPrior μ₀ η A χ ν₀)) x
        = conjExpPrior μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n) := sorry

/-- **The exponential-family marginal is a normalizer ratio** (single observation):
`m(x) = h(x) · Z(χ + T x, ν₀ + 1) / Z(χ, ν₀)`. No propriety needed — the `ℝ≥0∞` junk conventions
match on both sides. -/
theorem expFamily_predictiveDensity_eq_ratio
    -- LEAN-ONLY: measurability of the family components (regularity)
    (hη : Measurable η) (hA : Measurable A) (x : 𝓧) :
    predictiveDensity (expFamilyDensity η T A h) (conjExpPrior μ₀ η A χ ν₀) x
      = h x * (conjExpZ μ₀ η A (χ + T x) (ν₀ + 1) / conjExpZ μ₀ η A χ ν₀) := sorry

end StatLean.Bayesian
