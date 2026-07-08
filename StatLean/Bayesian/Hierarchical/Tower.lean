import StatLean.Bayesian.Hierarchical.Decomposition

/-!
# Hierarchical posterior tower and mixture identity

The mathematical heart of hierarchical Bayes: the parameter posterior is the hyperposterior-average
of the conditional posteriors,
$$\Pi(d\theta \mid x) = \int_\Lambda \Pi_\lambda(d\theta \mid x)\,\rho(d\lambda \mid x),$$
and posterior expectations obey the corresponding tower rule
`E[g(θ)∣x] = E_{λ∣x}[ E_{θ∣λ,x}[g(θ)] ]`. The same decomposition lifts to the posterior predictive.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.2.3 (conditional decompositions), pp. 465–467 (the mixture
representation of the hierarchical posterior).

**Proof formalization notes.** `posteriorExpectation_tower_hierarchical` is the pinned reverse
tower `posterior_comp` composed with the collapsed-vs-conditional bridge of `Decomposition`;
`thetaPosterior_apply_eq_lintegral_hyperPosterior` is that tower specialized to `g = 𝟙_s`
(the mixture identity in evaluated form); the predictive tower composes the response kernel `KY`
and pushes the mixture through `∫⁻`.

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

/-- **Posterior tower for the hierarchy** (3A.7): a posterior expectation is the hyperposterior
average of the conditional posterior expectations (Robert §10.2.3). -/
theorem posteriorExpectation_tower_hierarchical (g : Θ → ℝ≥0∞) (hg : Measurable g) :
    ∀ᵐ x ∂H.dataMarginal,
      ∫⁻ θ, g θ ∂((H.likelihood † H.mixPrior) x)
        = ∫⁻ lam, (∫⁻ θ, g θ ∂(H.conditionalPosterior lam x)) ∂(H.hyperPosterior x) := by
  sorry

/-- **The mixture identity** (3A.6, the single most important theorem of the batch), in evaluated
form: the parameter posterior of a set is the hyperposterior average of the conditional posteriors
of that set — `Π(s∣x) = ∫ Π_λ(s∣x) ρ(dλ∣x)` (Robert §10.2.3). -/
theorem thetaPosterior_apply_eq_lintegral_hyperPosterior {s : Set Θ} (hs : MeasurableSet s) :
    ∀ᵐ x ∂H.dataMarginal,
      (H.likelihood † H.mixPrior) x s
        = ∫⁻ lam, H.conditionalPosterior lam x s ∂(H.hyperPosterior x) := by
  sorry

/-- **Predictive tower** (3A.8): the hierarchical posterior predictive is the hyperposterior
average of the conditional posterior predictives (Robert §10.2.3). -/
theorem posteriorPredictive_hierarchical_tower (KY : Kernel Θ 𝓨) [IsMarkovKernel KY]
    {s : Set 𝓨} (hs : MeasurableSet s) :
    ∀ᵐ x ∂H.dataMarginal,
      (KY ∘ₖ (H.likelihood † H.mixPrior)) x s
        = ∫⁻ lam, (KY ∘ₖ H.conditionalPosterior lam) x s ∂(H.hyperPosterior x) := by
  sorry

end StatLean.Bayesian
