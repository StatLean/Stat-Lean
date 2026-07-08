import StatLean.Bayesian.Hierarchical.Decomposition

/-!
# Hierarchical posterior tower and mixture identity

The mathematical heart of hierarchical Bayes: the parameter posterior is the hyperposterior-average
of the conditional posteriors,
$$\Pi(d\theta \mid x) = \int_\Lambda \Pi_\lambda(d\theta \mid x)\,\rho(d\lambda \mid x),$$
and posterior expectations obey the corresponding tower rule
`E[g(θ)∣x] = E_{λ∣x}[ E_{θ∣λ,x}[g(θ)] ]`. The same decomposition lifts to the posterior predictive.

These are stated for a **dominated** hierarchical model (the setting the whole `StatLean.Bayesian`
area uses): the likelihood and prior kernels admit densities `p`, `q` against base measures `ν`, `μ`.
There the conditional posterior `Π_λ(·∣x)` is the density-form `generalizedPosterior p (Π_λ) x`
(equal a.e. to the abstract `conditionalPosterior λ x` by
`conditionalPosterior_givenHyper_ae_eq_generalizedPosterior`), which — unlike the abstract
measure-posterior — is jointly measurable in `(λ, x)`, so the outer hyperposterior integral is
well-behaved and the identity is a density Fubini computation.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.2.3 (conditional decompositions), pp. 465–467 (the mixture
representation of the hierarchical posterior).

**Proof formalization notes.** Both sides reduce, for data-marginal-a.e. `x`, to
`Z(x)⁻¹ · ∫λ ∫θ g(θ)·p(θ,x)·q(λ,θ) ∂μ ∂ρ` with `Z(x) = predictiveDensity p (mixPrior) x`. LHS:
`posterior_ae_eq_generalizedPosterior` turns `(K†Π)x` into the density form, `lintegral_bind`
expands `mixPrior = Π_• ∘ₘ ρ`, and `hpri` unfolds `Π_λ = μ.withDensity (q λ)`. RHS:
`hyperPosterior_ae_eq_generalizedPosterior` (the collapsed likelihood
`K∘ₖΠ_• = ν.withDensity (Z_•(x))` via the dominated predictive) turns the outer integral into a
`withDensity` against `ρ` with the per-`λ` normalizer `Z_λ(x)`, which **cancels** the conditional
normalizer inside; `∫λ Z_λ(x) ∂ρ = Z(x)` is `marginalLikelihood_hier_eq_lintegral_hyperMarginal`.
The abstract density-free versions need a jointly-measurable conditional-posterior kernel family
(a ForMathlib disintegration primitive; see `notes/bayesian/roadmap.md`, Batch 4).

**Bibliographic comments.** The mixture/tower decomposition of a hierarchical posterior is the
Rao–Blackwellization structure exploited by every hierarchical Gibbs sampler (Gelfand and Smith,
1990) and the basis of the "conditioning" justifications of the Stein effect (Robert §10.5); it is
the measure-theoretic content of the law of total (conditional) expectation applied to the
three-stage model of Lindley and Smith (1972).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Λ Θ 𝓧 𝓨 : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace 𝓧]
  [MeasurableSpace 𝓨] [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace Λ] [Nonempty Λ]
  (H : HierBayesExperiment Λ Θ 𝓧)

omit [StandardBorelSpace Λ] [Nonempty Λ] in
/-- **Collapsed-joint disintegration** (the measure-theoretic content the tower rests on): the
`(x, θ)`-joint disintegrates through the data marginal with the parameter posterior as its
conditional. This is `compProd_posterior_eq_map_swap` for the collapsed likelihood `K` against the
mixed prior `Π = priorKernel ∘ₘ hyperPrior`, rewritten through `dataMarginal_eq_comp_mixPrior`. -/
theorem dataMarginal_compProd_thetaPosterior_eq_map_swap :
    H.dataMarginal ⊗ₘ (H.likelihood † H.mixPrior)
      = (H.mixPrior ⊗ₘ H.likelihood).map Prod.swap := by
  rw [dataMarginal_eq_comp_mixPrior]
  exact compProd_posterior_eq_map_swap

/-- **Posterior tower for the dominated hierarchy** (3A.7): a posterior expectation is the
hyperposterior average of the conditional (density-form) posterior expectations
(Robert §10.2.3). -/
theorem posteriorExpectation_tower_hierarchical
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Robert §1.2 / §10.2.1
    (hlik : ∀ θ, H.likelihood θ = ν.withDensity (p θ))
    {μ : Measure Θ} [SFinite μ] {q : Λ → Θ → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the prior density (regularity)
    (hq : Measurable (Function.uncurry q))
    -- USER-INPUT: dominated prior kernel; Robert §10.2.1
    (hpri : ∀ lam, H.priorKernel lam = μ.withDensity (q lam))
    (g : Θ → ℝ≥0∞) (hg : Measurable g) :
    ∀ᵐ x ∂H.dataMarginal,
      ∫⁻ θ, g θ ∂((H.likelihood † H.mixPrior) x)
        = ∫⁻ lam, (∫⁻ θ, g θ ∂(generalizedPosterior p (H.priorKernel lam) x))
            ∂(H.hyperPosterior x) := by
  sorry

/-- **The mixture identity** (3A.6, the single most important theorem of the batch), in evaluated
form: the parameter posterior of a set is the hyperposterior average of the conditional posteriors
of that set — `Π(s∣x) = ∫ Π_λ(s∣x) ρ(dλ∣x)` (Robert §10.2.3). -/
theorem thetaPosterior_apply_eq_lintegral_hyperPosterior
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Robert §1.2 / §10.2.1
    (hlik : ∀ θ, H.likelihood θ = ν.withDensity (p θ))
    {μ : Measure Θ} [SFinite μ] {q : Λ → Θ → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the prior density (regularity)
    (hq : Measurable (Function.uncurry q))
    -- USER-INPUT: dominated prior kernel; Robert §10.2.1
    (hpri : ∀ lam, H.priorKernel lam = μ.withDensity (q lam))
    {s : Set Θ} (hs : MeasurableSet s) :
    ∀ᵐ x ∂H.dataMarginal,
      (H.likelihood † H.mixPrior) x s
        = ∫⁻ lam, generalizedPosterior p (H.priorKernel lam) x s ∂(H.hyperPosterior x) := by
  sorry

/-- **Predictive tower** (3A.8): the hierarchical posterior predictive is the hyperposterior
average of the conditional posterior predictives (Robert §10.2.3). -/
theorem posteriorPredictive_hierarchical_tower
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Robert §1.2 / §10.2.1
    (hlik : ∀ θ, H.likelihood θ = ν.withDensity (p θ))
    {μ : Measure Θ} [SFinite μ] {q : Λ → Θ → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the prior density (regularity)
    (hq : Measurable (Function.uncurry q))
    -- USER-INPUT: dominated prior kernel; Robert §10.2.1
    (hpri : ∀ lam, H.priorKernel lam = μ.withDensity (q lam))
    (KY : Kernel Θ 𝓨) [IsMarkovKernel KY] {s : Set 𝓨} (hs : MeasurableSet s) :
    ∀ᵐ x ∂H.dataMarginal,
      (KY ∘ₖ (H.likelihood † H.mixPrior)) x s
        = ∫⁻ lam, (KY ∘ₘ (generalizedPosterior p (H.priorKernel lam) x)) s
            ∂(H.hyperPosterior x) := by
  sorry

end StatLean.Bayesian
