import StatLean.Bayesian.Updating.Defs
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The posterior predictive is the conditional law of the future given the data

The theorem that justifies `posteriorPredictive`: under the joint Bayesian model
`(θ, x, y) ~ π ⊗ₘ (KX ×ₖ KY)` (parameter from the prior; data and future conditionally
independent given the parameter), the conditional law of the future `y` given the data `x` is the
posterior predictive:
$$\mathcal L(Y \mid X = x) = \int_\Theta K_Y(\theta, \cdot)\,\pi(d\theta \mid x)
  \qquad \text{for } (K_X \circ_m \pi)\text{-a.e. } x.$$
The mathematical pivot is the disintegration
`(KX ×ₖ KY) ∘ₘ π = (KX ∘ₘ π) ⊗ₘ posteriorPredictive KX KY π` — "data ⊗ predictive = joint of the
pair" — from which the `condDistrib` identification is uniqueness of disintegration.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §4.1.6, eq. (4.1.5), p. 172; §1.4 item (d), p. 22.

**Proof formalization notes.** The pivotal lemma is a rectangle (π-system) computation routed
through the pinned `compProd_posterior_eq_map_swap`: both sides evaluate on `A ×ˢ B` to
`∫⁻ θ, KX θ A * KY θ B ∂π`. The `condDistrib` statement then follows from the pinned uniqueness
lemma `condDistrib_ae_eq_of_measure_eq_compProd` applied to the coordinate maps on
`Θ × 𝓧 × 𝓨`, with marginal bookkeeping (`Measure.snd_compProd`, `Kernel.fst_prod`,
`Measure.map_map`); the future space `𝓨` must be standard Borel for `condDistrib` to exist.
Conditional independence of `x` and `y` given `θ` is encoded by the product kernel `KX ×ₖ KY` —
a constitutive modeling choice, not a regularity assumption.

**Bibliographic comments.** Reading prediction as conditioning in a joint model over parameter,
data, and future is the de Finetti–Geisser predictivist program (B. de Finetti, *Theory of
Probability*, 1974; S. Geisser, *Predictive Inference*, 1993) and the semantic basis of
probabilistic programming; Robert's eq. (4.1.5) is the textbook statement. The disintegration
technology is Kolmogorov (1933) and Doob (1953), as packaged by Mathlib's `condDistrib`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [m𝓨 : MeasurableSpace 𝓨]

/-- **Data ⊗ predictive = joint of the pair** (the pivotal disintegration behind Robert
eq. (4.1.5)): binding the prior through the pair experiment factors as the data marginal
`compProd` the posterior predictive. -/
theorem comp_prod_eq_compProd_posteriorPredictive
    [StandardBorelSpace Θ] [Nonempty Θ] {π : Measure Θ} [IsFiniteMeasure π]
    (KX : Kernel Θ 𝓧) [IsMarkovKernel KX] (KY : Kernel Θ 𝓨) [IsMarkovKernel KY] :
    (KX ×ₖ KY) ∘ₘ π = (KX ∘ₘ π) ⊗ₘ posteriorPredictive KX KY π := sorry

/-- **The posterior predictive is the conditional law of the future given the data**
(Robert eq. (4.1.5)): under `(θ, x, y) ~ π ⊗ₘ (KX ×ₖ KY)`, `condDistrib` of the future given the
data agrees with `posteriorPredictive`, predictive-a.e. -/
theorem condDistrib_ae_eq_posteriorPredictive
    [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    {π : Measure Θ} [IsFiniteMeasure π]
    (KX : Kernel Θ 𝓧) [IsMarkovKernel KX] (KY : Kernel Θ 𝓨) [IsMarkovKernel KY] :
    condDistrib (fun ω : Θ × 𝓧 × 𝓨 => ω.2.2) (fun ω => ω.2.1) (π ⊗ₘ (KX ×ₖ KY))
      =ᵐ[KX ∘ₘ π] posteriorPredictive KX KY π := sorry

end StatLean.Bayesian
