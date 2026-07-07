import Mathlib.Probability.Kernel.Posterior

/-!
# Posterior prediction — core data model (`posteriorPredictive`)

Data model for **Bayesian prediction**: having observed `x` from the experiment
`KX : Kernel Θ 𝓧`, the law of a future observation `y` from a second experiment
`KY : Kernel Θ 𝓨` sharing the same parameter is the **posterior predictive**
$$p(dy \mid x) = \int_\Theta K_Y(\theta, dy)\,\pi(d\theta \mid x),$$
i.e. the composition `KY ∘ₖ (KX†π)` of the future experiment with the posterior kernel.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §4.1.6, eq. (4.1.5) (the predictive distribution
`g^π(z|x) = ∫ g(z|x,θ) π(θ|x) dθ`), p. 172; §1.4 item (d), p. 22.

**Proof formalization notes.** Laptop-only data model — definitions only. `KX†π : Kernel 𝓧 Θ` and
`Kernel.comp : Kernel Θ 𝓨 → Kernel 𝓧 Θ → Kernel 𝓧 𝓨`, so `KY ∘ₖ (KX†π)` typechecks directly and
is Markov whenever `KY` is. The identification of this kernel with the conditional law of the
future given the data under the joint model — the theorem that justifies the definition — is
`StatLean.Bayesian.Updating.Predictive`.

**Bibliographic comments.** Prediction was the original use of inverse probability: Laplace's rule
of succession (1774) is a posterior predictive computation, formalized for the Beta–Bernoulli
model in `StatLean.Bayesian.Conjugacy.BetaBernoulli`. The predictive viewpoint — that inference
should be about observables — was championed by B. de Finetti (*Theory of Probability*, 1974) and
S. Geisser (*Predictive Inference: An Introduction*, Chapman & Hall, 1993); Robert presents the
predictive machine in §1.4 and eq. (4.1.5).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [m𝓨 : MeasurableSpace 𝓨]

/-- The **posterior predictive kernel** `x ↦ ∫ KY(θ, ·) π(dθ|x)`, as the composition
`KY ∘ₖ (KX†π)` (Robert eq. (4.1.5)). -/
noncomputable def posteriorPredictive [StandardBorelSpace Θ] [Nonempty Θ]
    (KX : Kernel Θ 𝓧) [IsFiniteKernel KX] (KY : Kernel Θ 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] : Kernel 𝓧 𝓨 :=
  KY ∘ₖ (KX†π)

/-- Pointwise form: the posterior predictive at `x` is the future experiment bound through the
posterior at `x`. -/
theorem posteriorPredictive_apply [StandardBorelSpace Θ] [Nonempty Θ]
    (KX : Kernel Θ 𝓧) [IsFiniteKernel KX] (KY : Kernel Θ 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] (x : 𝓧) :
    posteriorPredictive KX KY π x = KY ∘ₘ ((KX†π) x) := by unfold posteriorPredictive; rw [Kernel.comp_apply]

instance [StandardBorelSpace Θ] [Nonempty Θ]
    (KX : Kernel Θ 𝓧) [IsFiniteKernel KX] (KY : Kernel Θ 𝓨) [IsMarkovKernel KY]
    (π : Measure Θ) [IsFiniteMeasure π] :
    IsMarkovKernel (posteriorPredictive KX KY π) := by
  unfold posteriorPredictive; infer_instance

end StatLean.Bayesian
