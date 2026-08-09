import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Conditioning on a discrete random variable — the algebra of covariate cells

Theorem-agnostic toolkit for conditioning on the level sets of a map `X : Ω → 𝒳` with `𝒳`
a finite type: the law of total expectation over the cells, the two-arm split inside a
cell, and the factorization of an expectation under independence. Everything is phrased
with `ProbabilityTheory.cond` (`μ[|s]`), so a "conditional expectation given `X = x`" is
an ordinary Bochner integral.

Main results:

* `integral_eq_sum_cell` — `∫ f dμ = ∑ₓ μ(X = x) · ∫ f d(μ[|X = x])`.
* `integral_cell_eq_arm_split` — inside a cell, `∫ f d(μ[|X = x])` splits over `{Z = 1}`
  and `{Z = 0}` with weights `e(x)` and `1 - e(x)`.
* `integral_cond_indepFun_mul_ind` — under independence of `y` and `Z` in a cell,
  `∫ 1{Z = z}·y = P(Z = z)·∫ y`.

**Reference.** Standard measure-theoretic bookkeeping; no textbook result is being
formalized here. The statistical use is P. Ding, *A First Course in Causal Inference*,
arXiv:2305.18793v2, 2023, §10.3.1 eq. (10.8), where identification formulas are written
as finite sums over the values of a discrete covariate. (`Ding §10.3.1`.)

**Proof formalization notes.**

* `ProbabilityTheory.cond μ s = (μ s)⁻¹ • μ.restrict s`, so `∫ f d(μ[|s])` equals
  `(μ s).toReal⁻¹ • ∫ x in s, f x ∂μ`; that identity (`integral_cond_eq_setIntegral`) is
  the bridge every other lemma in this file uses.
* Null cells: `cond` scales by `(μ s)⁻¹ = ∞`, but the `toReal` route makes the value `0`;
  the decomposition lemmas are stated so that null cells contribute `0` on both sides, so
  no positivity hypotheses are needed for the *sums*. Positivity is required only where a
  single cell's conditional expectation is claimed to equal something.
* The cells `X ⁻¹' {x}` for `x : 𝒳` are pairwise disjoint with union `univ`, so the
  decomposition is `MeasureTheory.integral_fintype`-style over a finite partition.

**Bibliographic comments.** None: this is infrastructure, not a book result.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳]
  {μ : Measure Ω}

/-- Integration against a conditional measure is the set integral rescaled by the mass of
the conditioning event. -/
theorem integral_cond_eq_setIntegral (s : Set Ω) (f : Ω → ℝ) :
    ∫ ω, f ω ∂(μ[|s]) = (μ s).toReal⁻¹ * ∫ ω in s, f ω ∂μ := by
  sorry

/-- The mass of a conditioning event times its conditional integral is the set integral
— the form used to reassemble a decomposition, valid even when the event is null. -/
theorem measureReal_mul_integral_cond {s : Set Ω} (hs : μ s ≠ ⊤) (f : Ω → ℝ) :
    (μ s).toReal * ∫ ω, f ω ∂(μ[|s]) = ∫ ω in s, f ω ∂μ := by
  sorry

/-- **Law of total expectation over a discrete covariate**: an integral is the
cell-probability-weighted sum of the within-cell conditional integrals. -/
theorem integral_eq_sum_cell [Fintype 𝒳] [MeasurableSingletonClass 𝒳]
    [IsFiniteMeasure μ] {X : Ω → 𝒳}
    -- USER-INPUT: the covariate is a random variable; user-supplied data
    (hX : Measurable X) {f : Ω → ℝ}
    -- USER-INPUT: integrability of the integrand; needed for the additivity of the integral
    (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ x : 𝒳, (μ (X ⁻¹' {x})).toReal * ∫ ω, f ω ∂(μ[|X ⁻¹' {x}]) := by
  sorry

/-- **Two-arm split inside a cell**: conditioning further on the treatment splits a
within-cell conditional integral into the propensity-weighted average of the two arm
conditional integrals. -/
theorem integral_cond_cell_eq_arm_split [MeasurableSingletonClass 𝒳] [IsFiniteMeasure μ]
    {X : Ω → 𝒳} {Z : Ω → Bool}
    -- USER-INPUT: covariate and treatment are random variables; user-supplied data
    (hX : Measurable X) (hZ : Measurable Z) {f : Ω → ℝ}
    -- USER-INPUT: integrability of the integrand
    (hf : Integrable f μ) (x : 𝒳) :
    ∫ ω, f ω ∂(μ[|X ⁻¹' {x}])
      = ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal
            * ∫ ω, f ω ∂(μ[|{ω | Z ω = true} ∩ X ⁻¹' {x}])
        + ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal
            * ∫ ω, f ω ∂(μ[|{ω | Z ω = false} ∩ X ⁻¹' {x}]) := by
  sorry

/-- The two arm probabilities inside a cell sum to one on a cell of positive mass. -/
theorem cond_treated_add_cond_control [MeasurableSingletonClass 𝒳] [IsFiniteMeasure μ]
    {X : Ω → 𝒳} {Z : Ω → Bool} (hX : Measurable X) (hZ : Measurable Z) {x : 𝒳}
    -- USER-INPUT: a cell of positive probability; on a null cell both sides are `0`
    (hpos : μ (X ⁻¹' {x}) ≠ 0) :
    ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal
        + ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal = 1 := by
  sorry

/-- **Factorization under independence**: if `y` and `Z` are independent under a measure,
the expectation of `y` restricted to an arm factors into the arm probability times the
unrestricted expectation of `y`. This is the workhorse turning unconfoundedness into
identification. -/
theorem integral_ind_mul_of_indepFun {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → ℝ} {Z : Ω → Bool}
    -- USER-INPUT: independence of the potential outcome and the treatment (unconfoundedness)
    (hindep : IndepFun y Z ν)
    -- USER-INPUT: the potential outcome is integrable
    (hy : Integrable y ν)
    -- USER-INPUT: measurability of the two variables
    (hym : Measurable y) (hZ : Measurable Z) (z : Bool) :
    ∫ ω, (if Z ω = z then (1 : ℝ) else 0) * y ω ∂ν
      = (ν {ω | Z ω = z}).toReal * ∫ ω, y ω ∂ν := by
  sorry

/-- Consequence of the previous lemma in conditional form: under independence, the
conditional expectation of `y` given an arm equals its unconditional expectation. -/
theorem integral_cond_arm_eq_of_indepFun {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → ℝ} {Z : Ω → Bool} (hindep : IndepFun y Z ν) (hy : Integrable y ν)
    (hym : Measurable y) (hZ : Measurable Z) {z : Bool}
    -- USER-INPUT: the arm has positive probability; on a null arm the left side is `0`
    (hpos : ν {ω | Z ω = z} ≠ 0) :
    ∫ ω, y ω ∂(ν[|{ω | Z ω = z}]) = ∫ ω, y ω ∂ν := by
  sorry

end StatLean.CausalInference
