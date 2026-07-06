import StatLean.Bayesian.Decision.BayesEstimator

/-!
# The posterior mode (MAP) is the Bayes estimator under 0–1 loss (Robert §2.5.3 / §4.1.2)

On a finite parameter space, under the 0–1 loss `ℓ(θ, a) = 𝟙[θ ≠ a]`, the posterior mode (MAP
estimator) is a Bayes estimator. The mechanism is that the posterior 0–1 risk of action `a` is
`1 − π({a} | x)`, so minimizing it means maximizing the posterior mass.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §2.5.3, eq. (2.5.5)
and Proposition 2.5.7 (0–1 loss picks the most probable hypothesis), p. 81; §4.1.2 (MAP estimator
= posterior mode), p. 166.

**Proof formalization notes.** `lintegral_zeroOneLoss_eq` gives `∫ 𝟙[θ ≠ a] dρ = 1 − ρ{a}` (via
`lintegral_indicator` and `prob_compl_eq_one_sub`); since `1 − ·` is antitone
(`tsub_le_tsub_left`), an a.e. posterior-mass maximizer minimizes posterior 0–1 risk, and
`isBayesEstimator_of_ae_argmin` (our Robert Thm 2.3.2) finishes. Existence uses the choice-free
`fintypeArgmax`, whose measurable-selection lemma `measurable_fintypeArgmax` comes from
`measurable_to_countable'` and the finite Boolean combination of comparison sets (via
`fintypeArgmax_eq_iff`). Parameter space carries `[Fintype Θ] [Nonempty Θ]
[DiscreteMeasurableSpace Θ]`, so `StandardBorelSpace Θ` is automatic.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}

/-! ### `fintypeArgmax` API -/

/-- Every value is `≤` the value at the argmax. -/
theorem le_fintypeArgmax [Fintype Θ] [Nonempty Θ] (g : Θ → ℝ≥0∞) (b : Θ) :
    g b ≤ g (fintypeArgmax g) := sorry

/-- Characterization of the argmax: it is a maximizer, and least (in the canonical enumeration)
among maximizers. -/
theorem fintypeArgmax_eq_iff [Fintype Θ] [Nonempty Θ] (g : Θ → ℝ≥0∞) (a : Θ) :
    fintypeArgmax g = a ↔
      (∀ b, g b ≤ g a) ∧ ∀ a', (∀ b, g b ≤ g a') → Fintype.equivFin Θ a ≤ Fintype.equivFin Θ a' :=
  sorry

/-- Measurable selection: an argmax over finitely many measurable `ℝ≥0∞` coordinates is
measurable. -/
theorem measurable_fintypeArgmax [Fintype Θ] [Nonempty Θ] [DiscreteMeasurableSpace Θ]
    {g : 𝓧 → Θ → ℝ≥0∞}
    -- LEAN-ONLY: each coordinate is measurable (regularity)
    (hg : ∀ a, Measurable fun x => g x a) :
    Measurable fun x => fintypeArgmax (g x) := sorry

/-! ### Posterior 0–1 risk and the MAP estimator -/

/-- The 0–1 loss is jointly measurable on a countable parameter space. -/
theorem measurable_uncurry_zeroOneLoss [Countable Θ] [MeasurableSingletonClass Θ] :
    Measurable (Function.uncurry (zeroOneLoss (α := Θ))) := sorry

/-- Posterior 0–1 risk is one minus the posterior mass: `∫ 𝟙[θ ≠ a] dρ = 1 − ρ{a}`
(Robert §2.5.3, the mechanism of Proposition 2.5.7). -/
theorem lintegral_zeroOneLoss_eq [MeasurableSingletonClass Θ]
    (ρ : Measure Θ) [IsProbabilityMeasure ρ] (a : Θ) :
    ∫⁻ θ, zeroOneLoss θ a ∂ρ = 1 - ρ {a} := sorry

/-- The posterior mode is measurable. -/
theorem measurable_posteriorMode [Fintype Θ] [Nonempty Θ] [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Measurable (posteriorMode P π) := sorry

/-- Any measurable a.e.-maximizer of the posterior mass is a Bayes estimator under 0–1 loss
(the criterion behind Robert Proposition 2.5.7). -/
theorem isBayesEstimator_of_ae_argmax_posterior [Fintype Θ] [Nonempty Θ]
    [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    -- LEAN-ONLY: the estimator is measurable
    {δ : 𝓧 → Θ} (hδ : Measurable δ)
    -- USER-INPUT: `δ(x)` maximizes the posterior mass for predictive-a.e. `x`; Robert Prop. 2.5.7
    (hmax : ∀ᵐ x ∂(P ∘ₘ π), ∀ b, (P†π) x {b} ≤ (P†π) x {δ x}) :
    IsBayesEstimator zeroOneLoss P (Kernel.deterministic δ hδ) π := sorry

/-- **The posterior mode (MAP) is a Bayes estimator under 0–1 loss** on a finite parameter space
(Robert Proposition 2.5.7 / §4.1.2). -/
theorem posteriorMode_isBayesEstimator_zeroOneLoss [Fintype Θ] [Nonempty Θ]
    [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    IsBayesEstimator zeroOneLoss P
      (Kernel.deterministic (posteriorMode P π) (measurable_posteriorMode P π)) π := sorry

end StatLean.Bayesian
