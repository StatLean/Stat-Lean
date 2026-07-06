import StatLean.Bayesian.Dominated.Defs

/-!
# The prior predictive density and its regularity

For a dominated model `κ θ = ν.withDensity (p θ)` with prior `π`, this file establishes that the
data distribution has the prior predictive density `m` with respect to `ν`,
$$\kappa \circ_m \pi = \nu.\mathrm{withDensity}\,(m), \qquad m(x) = \int_\Theta p(\theta,x)\,\pi(d\theta),$$
together with the measurability of `m` and the a.e. non-degeneracy facts (`0 < m < ∞`) that hold
automatically under a finite model.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §1.4, the marginal
`m(x) = ∫ f(x|θ) π(dθ)`, p. 22.

**Proof formalization notes.** `m`'s finiteness (`ν`-a.e. and `(κ ∘ₘ π)`-a.e.) and positivity
(`(κ ∘ₘ π)`-a.e.) are **derived** from `IsFiniteMeasure (κ ∘ₘ π)` and the withDensity
representation — they are *not* hypotheses (assuming `0 < m` would be laundering a fact forced by
the setup). Key Mathlib bricks: `Measurable.lintegral_prod_left'`, `Measure.bind_apply`,
`MeasureTheory.withDensity_apply`, `lintegral_eq_zero_iff`, `ae_lt_top`,
`withDensity_absolutelyContinuous`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {κ : Kernel Θ 𝓧} {π : Measure Θ} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ≥0∞}

/-- The prior predictive density is measurable. -/
theorem measurable_predictiveDensity [SFinite π]
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (predictiveDensity p π) := sorry

/-- Where the predictive density vanishes, the likelihood section is `π`-a.e. zero. -/
theorem likelihood_ae_eq_zero_of_predictiveDensity_eq_zero [SFinite π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) {x : 𝓧} (hx : predictiveDensity p π x = 0) :
    (fun θ => p θ x) =ᵐ[π] 0 := sorry

/-- **The data distribution has the prior predictive density** `m` with respect to `ν`:
`κ ∘ₘ π = ν.withDensity (predictiveDensity p π)` (Robert §1.4, the marginal `m(x)`). -/
theorem comp_eq_withDensity_predictiveDensity [SFinite π] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model, K(θ, ·) = p(θ, ·) ν; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    κ ∘ₘ π = ν.withDensity (predictiveDensity p π) := sorry

/-- Forced by finiteness of the data distribution: `m < ∞` holds `ν`-a.e. (not a hypothesis). -/
theorem predictiveDensity_lt_top_ae [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂ν, predictiveDensity p π x < ∞ := sorry

/-- `m < ∞` holds `(κ ∘ₘ π)`-a.e. (transferred along `κ ∘ₘ π = ν.withDensity m ≪ ν`). -/
theorem predictiveDensity_lt_top_ae_comp [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), predictiveDensity p π x < ∞ := sorry

/-- `m > 0` holds `(κ ∘ₘ π)`-a.e.: the data distribution charges no set where its own density
vanishes (not a hypothesis). -/
theorem predictiveDensity_pos_ae [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), 0 < predictiveDensity p π x := sorry

end StatLean.Bayesian
