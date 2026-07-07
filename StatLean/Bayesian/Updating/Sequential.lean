import StatLean.Bayesian.GeneralizedBayes.Defs
import StatLean.Bayesian.Dominated.PredictiveDensity

/-!
# Sequential Bayes and reparameterization equivariance

Two coherence properties of Bayesian updating:

* **Sequential Bayes** (Robert eq. (1.4.1)): updating on `x` and then on `y` equals updating once
  on the joint observation `(x, y)` — for a dominated pair experiment `κ₁ ×ₖ κ₂`,
  $$\big((\kappa_1 \times \kappa_2)^{\dagger}_\pi\big)(x, y)
    = \big(\pi_x\big)_y \qquad \text{predictive-a.e.},$$
  where `π_x` is the generalized posterior for the first coordinate;
* **Reparameterization equivariance**: for a measurable equivalence `φ : Θ ≃ᵐ Θ'`, the posterior
  transforms by pushforward, `(κ.comap φ.symm)†(π.map φ) = ((κ†π) ·).map φ` predictive-a.e.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.4, eq. (1.4.1) (sequential coherence of the posterior), p. 23;
the equivariance of the Bayesian answer under reparameterization is the §1.3 invariance discussion
(and underlies the §3.5 noninformative-prior program).

**Proof formalization notes.** Sequential: the pair kernel is dominated by `ν₁.prod ν₂` with the
product density (pinned `prod_withDensity_left/right` + `withDensity_mul`); apply the Batch-1
headline and rearrange with `ENNReal` algebra; the first-coordinate nondegeneracy `0 < m₁ < ∞`
transports along `Prod.fst` (`Kernel.fst_prod`, `Measure.map_comp`). Reparameterization is
abstract (no domination): verify the disintegration property of `((κ†π) ·).map φ` with
`ae_eq_posterior_of_compProd_eq`, `Measure.compProd_map`, and the rectangle lemma
`map_compProd_comap` below.

**Bibliographic comments.** Sequential coherence — today's posterior is tomorrow's prior — is the
operational heart of Bayesian learning, already used by Laplace and stressed axiomatically by
B. de Finetti (1937) and D. V. Lindley (*Introduction to Probability and Statistics from a
Bayesian Viewpoint*, Cambridge, 1965). Equivariance under reparameterization is the invariance
desideratum behind Jeffreys's priors (H. Jeffreys, *Theory of Probability*, 1939; Robert §3.5).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ Θ' 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [mΘ' : MeasurableSpace Θ']
  [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]

/-- **Sequential Bayes** (Robert eq. (1.4.1)), dominated form: the posterior of the pair
experiment at `(x, y)` is the `y`-update of the `x`-posterior, predictive-a.e. -/
theorem posterior_prod_ae_eq_sequential
    [StandardBorelSpace Θ] [Nonempty Θ] {π : Measure Θ} [IsFiniteMeasure π]
    {κ₁ : Kernel Θ 𝓧} [IsMarkovKernel κ₁] {κ₂ : Kernel Θ 𝓨} [IsMarkovKernel κ₂]
    {ν₁ : Measure 𝓧} [SigmaFinite ν₁] {ν₂ : Measure 𝓨} [SigmaFinite ν₂]
    {p₁ : Θ → 𝓧 → ℝ≥0∞} {p₂ : Θ → 𝓨 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the two densities (regularity)
    (hp₁ : Measurable (Function.uncurry p₁)) (hp₂ : Measurable (Function.uncurry p₂))
    -- USER-INPUT: both coordinates are dominated models; Robert Definition 1.2.1 / §1.4
    (hκ₁ : ∀ θ, κ₁ θ = ν₁.withDensity (p₁ θ)) (hκ₂ : ∀ θ, κ₂ θ = ν₂.withDensity (p₂ θ)) :
    ∀ᵐ q ∂((κ₁ ×ₖ κ₂) ∘ₘ π),
      ((κ₁ ×ₖ κ₂)†π) q = generalizedPosterior p₂ (generalizedPosterior p₁ π q.1) q.2 := sorry

/-- Change of prior variables through `compProd` (rectangle computation). -/
theorem map_compProd_comap (φ : Θ ≃ᵐ Θ') (κ : Kernel Θ 𝓧) [IsSFiniteKernel κ]
    (π : Measure Θ) [SFinite π] :
    (π.map φ) ⊗ₘ (κ.comap φ.symm φ.symm.measurable) = (π ⊗ₘ κ).map (Prod.map φ id) := sorry

/-- **Reparameterization equivariance of the posterior** (Robert §1.3/§3.5 invariance): for a
measurable equivalence of parameter spaces, the posterior of the reparameterized experiment is the
pushforward of the original posterior, predictive-a.e. -/
theorem posterior_comap_map_ae_eq_map_posterior
    [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace Θ'] [Nonempty Θ']
    {π : Measure Θ} [IsFiniteMeasure π] (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (φ : Θ ≃ᵐ Θ') :
    ∀ᵐ x ∂(κ ∘ₘ π),
      ((κ.comap φ.symm φ.symm.measurable)†(π.map φ)) x = ((κ†π) x).map φ := sorry

end StatLean.Bayesian
