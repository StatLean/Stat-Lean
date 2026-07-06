import StatLean.Bayesian.Dominated.PredictiveDensity

/-!
# Bayes' theorem in dominated form (posterior density)

The central theorem of Bayesian inference in the dominated setting: for predictive-almost-every
data `x`, the posterior is the prior reweighted by the normalized likelihood density,
$$\pi(d\theta \mid x) = \frac{p(\theta, x)\,\pi(d\theta)}{\int_\Theta p(\theta', x)\,\pi(d\theta')}.$$

The proof identifies the explicit density kernel `bayesKernel p π` with Mathlib's abstract
posterior `κ†π`, via the disintegration identity
`(κ ∘ₘ π) ⊗ₘ bayesKernel p π = (π ⊗ₘ κ).map Prod.swap` and the uniqueness of disintegrations
(`ae_eq_posterior_of_compProd_eq`).

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §1.2, eq. (1.2.3)
(the posterior density), p. 9; §1.4, p. 22.

**Proof formalization notes.** The headline `compProd_bayesKernel_eq_map_swap` is a π-system
computation on measurable rectangles. `IsFiniteKernel (bayesKernel p π)` is proved unconditionally
(the total mass is `≤ 1` where measurable, and the junk branch of `Kernel.withDensity` is the zero
kernel). No `IsMarkovKernel κ` is required — `bayesKernel` self-normalizes. `SFinite ν` is needed
for the Tonelli/withDensity manipulations. Watch CLAUDE.md gotcha 12: after
`lintegral_withDensity_eq_lintegral_mul` the integrand is un-β-reduced — use `simp_rw`. Key
bricks: `ext_of_generate_finite`, `generateFrom_prod`, `isPiSystem_prod`,
`Measure.compProd_apply_prod`, `Measure.map_apply`, `Set.preimage_swap_prod`,
`Kernel.withDensity_apply'`, `ae_eq_posterior_of_compProd_eq`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  {κ : Kernel Θ 𝓧} {π : Measure Θ} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ≥0∞}

/-- The posterior density is jointly measurable. -/
theorem measurable_uncurry_bayesDensity [SFinite π]
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (Function.uncurry (bayesDensity p π)) := sorry

/-- The Bayes kernel evaluated at `x` is the prior reweighted by the posterior density. -/
theorem bayesKernel_apply [IsFiniteMeasure π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) (x : 𝓧) :
    bayesKernel p π x = π.withDensity (bayesDensity p π x) := sorry

/-- The Bayes kernel is sub-Markov: total mass `≤ 1` (mass `1` where `0 < m x < ∞`, else `0`). -/
theorem bayesKernel_apply_univ_le_one [IsFiniteMeasure π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) (x : 𝓧) :
    bayesKernel p π x Set.univ ≤ 1 := sorry

/-- The Bayes kernel is a finite kernel (unconditionally — the non-measurable branch is `0`). -/
instance [IsFiniteMeasure π] : IsFiniteKernel (bayesKernel p π) := sorry

/-- Pointwise heart of the disintegration: for `ν`-a.e. `x`,
`m x * ∫_s (p(·,x)/m x) dπ = ∫_s p(·,x) dπ`. -/
theorem predictiveDensity_mul_setLIntegral_bayesDensity
    [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    -- LEAN-ONLY: the target parameter set is measurable
    {s : Set Θ} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ν, predictiveDensity p π x * ∫⁻ θ in s, bayesDensity p π x θ ∂π
      = ∫⁻ θ in s, p θ x ∂π := sorry

/-- **The prior×likelihood disintegration**: `predictive ⊗ posterior-candidate = joint (swapped)`.
This is the "prior × likelihood = predictive × posterior" identity for the explicit density
kernel. -/
theorem compProd_bayesKernel_eq_map_swap [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    (κ ∘ₘ π) ⊗ₘ bayesKernel p π = (π ⊗ₘ κ).map Prod.swap := sorry

/-- Uniqueness of disintegration: the explicit density kernel IS the abstract posterior,
`(κ ∘ₘ π)`-a.e. -/
theorem bayesKernel_ae_eq_posterior [StandardBorelSpace Θ] [Nonempty Θ]
    [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    bayesKernel p π =ᵐ[κ ∘ₘ π] κ†π := sorry

/-- **Bayes' theorem, dominated form** (Robert eq. (1.2.3)): for predictive-a.e. `x`,
`π(dθ | x) = p(θ,x) π(dθ) / ∫ p(θ',x) π(dθ')`. -/
theorem posterior_eq_withDensity_likelihood_div_predictive
    [StandardBorelSpace Θ] [Nonempty Θ] [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density (measure-theoretic regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model, K(θ, ·) = p(θ, ·) ν; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x = π.withDensity fun θ => p θ x / ∫⁻ θ', p θ' x ∂π := sorry

end StatLean.Bayesian
