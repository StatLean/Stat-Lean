import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Laplace-transform uniqueness on a set with nonempty interior (`s` dimensions)

The `s`-dimensional analogue of the one-dimensional statements: two finite measures on
`EuclideanSpace ℝ (Fin s)` whose Laplace transforms `t ↦ ∫ e^{⟪t, x⟫} dμ(x)` are finite and
agree on a set `S` with an interior point are equal, together with the signed corollary for a
function whose weighted integrals vanish on `S`.

* `ext_of_integral_exp_inner_eqOn` — measure uniqueness;
* `ae_eq_zero_of_integral_exp_inner_eq_zero` — the signed corollary.

The multivariate form is what completeness of an `s`-parameter full-rank exponential family
consumes: the natural parameter set has nonempty interior in `ℝ^s`, and the vanishing
condition on an unbiased estimator of `0` holds only there.

**Reference.** Classical Laplace-transform uniqueness; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* **Route.** Fix `t₀ ∈ interior S` and a small box `t₀ + (-ε, ε)^s ⊆ S`. Recenter by tilting
  both measures at `t₀`, so that both become probability measures (the degenerate branch
  `μ = 0` is separated first, `e^{⟪t₀,x⟫} > 0` forcing `∫ e^{⟪t₀,x⟫} dμ = 0 ↔ μ = 0`). Then
  continue **one coordinate at a time**: with the other `s - 1` coordinates frozen at real
  values inside the box, `z ↦ ∫ exp(⟪t, x⟫ + z·xᵢ) dμ` is analytic on the vertical strip
  `|Re z| < ε` (dominated differentiation, as in `analyticOnNhd_complexMGF`), the two such
  functions agree on the real segment `(-ε, ε)`, hence agree on the whole strip by the
  identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`; evaluating at
  `z = -I·vᵢ` moves coordinate `i` to the imaginary axis. Iterating over `i = 1, …, s` moves
  all coordinates, producing equality of the two characteristic functions at every
  `v ∈ ℝ^s`. `MeasureTheory.Measure.ext_of_charFun` (available since
  `EuclideanSpace ℝ (Fin s)` is a complete second-countable real inner-product space) closes,
  and untilting via `MeasureTheory.withDensity_inv_same` returns to the original measures.
* The prose template for the per-coordinate strip continuation is
  `StatLean/AsymptoticStatistics/ForMathlib/BivariateMGFUniqueness.lean` (`s = 2` with one
  coordinate already on the imaginary axis). It is deliberately **not** imported: this file
  belongs to the `ForMathlib` layer, whose imports stay Mathlib-only, and the bivariate file
  is specialized to the Gaussian-marginal hypothesis it was written for.
* The carrier is `EuclideanSpace ℝ (Fin s)` rather than `Fin s → ℝ` so that `⟪·, ·⟫_ℝ` and
  `Measure.ext_of_charFun` are available without a `WithLp` transport step.
* The integrability side conditions are kept explicit: without them the Bochner integrals are
  junk-valued `0` and the conclusions are false.

**Bibliographic comments.** The one-dimensional statement is due to M. Lerch ("Sur un point
de la théorie des fonctions génératrices d'Abel," *Acta Math.* **27** (1903), 339–351); the
strip-analyticity technique and the multidimensional extension follow D. V. Widder (*The
Laplace Transform*, Princeton University Press, 1941, Ch. II and VI).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {s : ℕ}

/-- **Multivariate Laplace-transform uniqueness, local form.** Two finite measures on
`EuclideanSpace ℝ (Fin s)` whose Laplace transforms are finite and agree on a set `S` with an
interior point coincide. -/
theorem ext_of_integral_exp_inner_eqOn
    -- USER-INPUT: the two measures being compared; genuine external data
    {μ ν : Measure (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: both are finite; required by `Measure.ext_of_charFun` and by the tilt
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    -- USER-INPUT: the parameter set on which the transforms are compared; free choice
    {S : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: `S` has an interior point; supplies the box for the coordinatewise
    -- analytic continuation
    (hS : (interior S).Nonempty)
    -- USER-INPUT: finiteness of the transform of `μ` on `S`; else `∫` is junk-valued `0`
    (hμ : ∀ t ∈ S, Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) μ)
    -- USER-INPUT: finiteness of the transform of `ν` on `S`
    (hν : ∀ t ∈ S, Integrable (fun x => Real.exp ⟪t, x⟫_ℝ) ν)
    -- USER-INPUT: the two Laplace transforms agree on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, Real.exp ⟪t, x⟫_ℝ ∂μ = ∫ x, Real.exp ⟪t, x⟫_ℝ ∂ν) :
    μ = ν := by
  sorry

/-- **Multivariate signed corollary.** If the `e^{⟪t, x⟫}`-weighted integrals of a measurable
`f` vanish for every `t` in a set with an interior point, then `f` vanishes almost
everywhere. This is the analytic core of completeness for `s`-parameter full-rank exponential
families. -/
theorem ae_eq_zero_of_integral_exp_inner_eq_zero
    -- USER-INPUT: the reference measure; free choice
    {ν : Measure (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: σ-finiteness; needed to read an a.e. equality off equal `withDensity`s
    [SigmaFinite ν]
    -- USER-INPUT: the candidate function (an unbiased estimator of `0` in applications)
    {f : EuclideanSpace ℝ (Fin s) → ℝ} (hf : Measurable f)
    -- USER-INPUT: the parameter set; free choice
    {S : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: `S` has an interior point; supplies the analytic-continuation box
    (hS : (interior S).Nonempty)
    -- USER-INPUT: the weighted integrals exist on `S`; else `∫` is junk-valued `0`
    (hint : ∀ t ∈ S, Integrable (fun x => f x * Real.exp ⟪t, x⟫_ℝ) ν)
    -- USER-INPUT: the weighted integrals vanish on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, f x * Real.exp ⟪t, x⟫_ℝ ∂ν = 0) :
    f =ᵐ[ν] 0 := by
  sorry

end StatLean.PointEstimation
