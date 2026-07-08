import Mathlib.Probability.Kernel.Posterior

/-!
# Hierarchical Bayesian model — core data model (`HierBayesExperiment`)

A **two-level hierarchical Bayesian model** bundles a hyperprior on a hyperparameter space `Λ`, a
prior kernel taking a hyperparameter to a prior on the parameter space `Θ`, and a likelihood kernel
taking a parameter to a data distribution on `𝓧`:
$$\lambda \sim \rho, \qquad \theta \mid \lambda \sim \Pi_\lambda, \qquad X \mid \theta \sim K_\theta.$$
Everything downstream — the mixed (marginal) prior, the data marginal, the hyperposterior, and the
conditional posteriors given a hyperparameter — is built from these three ingredients.

From `HierBayesExperiment H` this file names:

* `mixPrior H = priorKernel ∘ₘ hyperPrior` — the **marginal prior on `Θ`** obtained by integrating
  out the hyperparameter (Robert's incompletely specified prior, §10.1);
* `dataMarginal H = (likelihood ∘ₖ priorKernel) ∘ₘ hyperPrior` — the **prior predictive on `𝓧`**;
* `hyperPosterior H = (likelihood ∘ₖ priorKernel) † hyperPrior` — the **posterior on the
  hyperparameter** given the data;
* `conditionalPosterior H λ = likelihood † (priorKernel λ)` — the **posterior on `Θ` for a fixed
  hyperparameter** `λ`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.1 (incompletely specified priors), p. 457; §10.2.1
(hierarchical models), Definition 10.2.1, p. 460; §10.2.3 (conditional decompositions), p. 465.

**Proof formalization notes.** Laptop-only data model — definitions only. `HierBayesExperiment`
carries the probability/Markov requirements as instance-typed fields (registered as instances),
because Robert's §10.2.1 constitutively demands a *probability* hyperprior and *Markov* prior and
likelihood kernels; dropping any makes the object not the hierarchical Bayesian model. The
regularity Mathlib's posterior requires — `StandardBorelSpace` and `Nonempty` on the space being
inferred — is Lean-side and attaches as typeclass arguments on `hyperPosterior`/`conditionalPosterior`,
not as structure fields. The derived objects are thin wrappers over Mathlib's `Measure.bind` (`∘ₘ`),
`Kernel.comp` (`∘ₖ`), and `ProbabilityTheory.posterior` (`†`); the substantive theorems live in
`Hierarchical.Decomposition` and `Hierarchical.Tower`.

**Bibliographic comments.** Hierarchical priors are due to I. J. Good (*The Estimation of
Probabilities*, MIT Press, 1965) and, in the modern Bayesian-linear-model form, to D. V. Lindley
and A. F. M. Smith, "Bayes estimates for the linear model," *J. Roy. Statist. Soc. Ser. B* 34
(1972), 1–41. The three-stage `hyperprior → prior → likelihood` structure and its conditional
decompositions are the subject of Robert Chapter 10; the measure-theoretic kernel formulation used
here rests on the standard-Borel disintegration theory underlying Mathlib's `posterior`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Λ Θ 𝓧 : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- A **two-level hierarchical Bayesian model** (Robert §10.2.1, Definition 10.2.1): a probability
hyperprior `ρ` on `Λ`, a Markov prior kernel `Π : Λ ⇝ Θ`, and a Markov likelihood kernel
`K : Θ ⇝ 𝓧`, realizing `λ ∼ ρ, θ∣λ ∼ Π_λ, X∣θ ∼ K_θ`. -/
structure HierBayesExperiment (Λ Θ 𝓧 : Type*) [MeasurableSpace Λ] [MeasurableSpace Θ]
    [MeasurableSpace 𝓧] where
  /-- The hyperprior `ρ` on the hyperparameter space `Λ`. -/
  hyperPrior : Measure Λ
  /-- The prior kernel `λ ↦ Π_λ`, a Markov kernel from hyperparameters to parameter priors. -/
  priorKernel : Kernel Λ Θ
  /-- The likelihood `θ ↦ K_θ`, a Markov kernel from parameters to data. -/
  likelihood : Kernel Θ 𝓧
  /-- Constitutive (Robert §10.2.1): the hyperprior is a *probability* distribution. -/
  hyperPriorIsProbability : IsProbabilityMeasure hyperPrior
  /-- Constitutive (Robert §10.2.1): each `Π_λ` is a probability distribution (Markov kernel). -/
  priorKernelIsMarkov : IsMarkovKernel priorKernel
  /-- Constitutive (Robert §10.2.1): each `K_θ` is a probability distribution (Markov kernel). -/
  likelihoodIsMarkov : IsMarkovKernel likelihood

attribute [instance] HierBayesExperiment.hyperPriorIsProbability
  HierBayesExperiment.priorKernelIsMarkov HierBayesExperiment.likelihoodIsMarkov

namespace HierBayesExperiment

variable (H : HierBayesExperiment Λ Θ 𝓧)

/-- The **marginal (mixed) prior** on `Θ`, `Π = ∫ Π_λ ρ(dλ) = priorKernel ∘ₘ hyperPrior`
(Robert §10.1, the incompletely specified prior). -/
noncomputable def mixPrior : Measure Θ := H.priorKernel ∘ₘ H.hyperPrior

/-- The **prior predictive (data marginal)** on `𝓧`, `m(x) = ∫∫ K_θ Π_λ(dθ) ρ(dλ)`
(Robert §10.2.2). -/
noncomputable def dataMarginal : Measure 𝓧 := (H.likelihood ∘ₖ H.priorKernel) ∘ₘ H.hyperPrior

/-- The **hyperposterior** `ρ(·|x)` on the hyperparameter, as the posterior of the collapsed
likelihood `K ∘ₖ Π : Λ ⇝ 𝓧` with respect to the hyperprior (Robert §10.2.3, eq. for `π(λ|x)`). -/
noncomputable def hyperPosterior [StandardBorelSpace Λ] [Nonempty Λ] : Kernel 𝓧 Λ :=
  (H.likelihood ∘ₖ H.priorKernel) † H.hyperPrior

/-- The **conditional posterior** `Π_λ(·|x)` on `Θ` for a fixed hyperparameter `λ`, as the
posterior of the likelihood with respect to the prior `Π_λ` (Robert §10.2.3). -/
noncomputable def conditionalPosterior [StandardBorelSpace Θ] [Nonempty Θ] (lam : Λ) :
    Kernel 𝓧 Θ :=
  H.likelihood † (H.priorKernel lam)

end HierBayesExperiment

end StatLean.Bayesian
