import StatLean.Bayesian.Experiment.Defs

/-!
# Bayesian model — basic properties and the posterior disintegration

Textbook-facing restatements, for a `BayesExperiment`, of Mathlib's posterior-kernel identities:

* `posterior_disintegrates_joint` — **predictive × posterior = joint (swapped)**, the core of
  Bayesian conditioning "prior × likelihood becomes predictive × posterior" (Robert §1.4);
* `posterior_comp_predictive` — composing the posterior with the predictive returns the prior.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §1.4 (a)–(d)
(joint, marginal, posterior, predictive), p. 22.

**Proof formalization notes.** These are *aliases* of pinned Mathlib theorems under
textbook-facing names — we `import` and reuse `ProbabilityTheory.compProd_posterior_eq_map_swap`
and `posterior_comp_self`, we do not reprove them. The probability/Markov instances follow from
the constitutive `BayesExperiment` fields through Mathlib's instance chains.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

namespace BayesExperiment

variable (E : BayesExperiment Θ 𝓧)

instance : IsProbabilityMeasure E.joint := sorry

instance : IsProbabilityMeasure E.predictive := sorry

instance [StandardBorelSpace Θ] [Nonempty Θ] : IsMarkovKernel E.posterior := sorry

/-- **The posterior disintegrates the joint distribution**: `predictive ⊗ₘ posterior` equals the
joint distribution with its coordinates swapped (Robert §1.4). Textbook alias of Mathlib's
`compProd_posterior_eq_map_swap`. -/
theorem posterior_disintegrates_joint [StandardBorelSpace Θ] [Nonempty Θ] :
    E.predictive ⊗ₘ E.posterior = E.joint.map Prod.swap := sorry

/-- Composing the posterior kernel with the prior predictive recovers the prior
(Robert §1.4). Textbook alias of Mathlib's `posterior_comp_self`. -/
theorem posterior_comp_predictive [StandardBorelSpace Θ] [Nonempty Θ] :
    E.posterior ∘ₘ E.predictive = E.prior := sorry

end BayesExperiment

end StatLean.Bayesian
