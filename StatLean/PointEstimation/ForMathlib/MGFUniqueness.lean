import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Laplace-transform uniqueness on a set with nonempty interior (one dimension)

Two finite measures on `ℝ` whose Laplace transforms `t ↦ ∫ e^{tx} dμ(x)` agree on a set `S`
with an interior point are equal. Mathlib knows the *probability-measure, global-`mgf`* form
(`ProbabilityTheory.eqOn_complexMGF_of_mgf` and its consequences); the statistical
applications need the **local** form, where equality of the transforms is only available on
the natural parameter set of an exponential family, and the measures are finite rather than
normalized.

This file provides:

* `ext_of_integral_exp_eqOn` — the measure-uniqueness statement;
* `ae_eq_zero_of_integral_exp_smul_eq_zero` — the **signed** corollary: a function whose
  `e^{tx}`-weighted integrals vanish on `S` is null. This is the analytic engine behind
  completeness of a full-rank exponential family (a candidate unbiased estimator of `0` has
  vanishing tilted integrals throughout the natural parameter set, hence vanishes a.e.).

**Reference.** Classical Laplace-transform uniqueness; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* **Route for `ext_of_integral_exp_eqOn`.** Pick `t₀ ∈ interior S`. Tilt both measures to
  `t₀` with `MeasureTheory.Measure.tilted`: the tilted measures are probability measures
  (or both zero, the degenerate branch handled separately, since `e^{t₀x} > 0` forces
  `∫ e^{t₀x} dμ = 0 ↔ μ = 0`). The tilted-mgf identity `integral_exp_tilted_mul` turns
  agreement of the two transforms on `S` into agreement of the two `mgf`s on the translate
  `S - t₀`, a set containing a neighbourhood of `0`. Strip analyticity of `complexMGF`
  (`ProbabilityTheory.analyticOnNhd_complexMGF`) plus the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) — packaged here as
  `eqOn_complexMGF_of_mgf_eqOn` — propagate the equality from that real segment to the whole
  vertical strip, in particular to the imaginary axis. There `complexMGF` evaluated at `I·u`
  is the characteristic function, so `MeasureTheory.Measure.ext_of_charFun` identifies the
  two tilted measures. Untilting is `MeasureTheory.withDensity_inv_same` (the tilting density
  `e^{t₀x}/Z` is measurable, strictly positive and finite, so `withDensity` by it is
  injective on measures).
* **Why the local `eqOn` helper is genuinely needed.** Mathlib's
  `ProbabilityTheory.eqOn_complexMGF_of_mgf` demands *global* equality `mgf X μ = mgf Y μ'`
  of the two real `mgf`s (a `funext`-level hypothesis). Our data only gives a `Set.EqOn` on
  `S`, and outside the common integrability set the two `mgf`s are junk-valued `0`, so the
  global hypothesis is unavailable. `eqOn_complexMGF_of_mgf_eqOn` re-runs the same identity
  theorem argument from a `Set.EqOn` hypothesis on an open nonempty `S` contained in both
  integrability sets, concluding on the intersection strip (which is connected because
  `ProbabilityTheory.convex_integrableExpSet` makes each factor an interval).
* **Route for the signed corollary.** Split `f = f⁺ - f⁻` and form the two finite measures
  `dμ^± = f^± e^{t₀ x} dν` for an interior point `t₀` (finite exactly because of the
  integrability hypothesis at `t₀`). Their Laplace transforms agree on `S - t₀`, so
  `ext_of_integral_exp_eqOn` gives `μ⁺ = μ⁻`; `SigmaFinite ν` then upgrades equality of the
  two `withDensity`s to `f⁺ e^{t₀·} =ᵐ[ν] f⁻ e^{t₀·}`, and positivity of `e^{t₀·}` gives
  `f⁺ =ᵐ[ν] f⁻`, i.e. `f =ᵐ[ν] 0`.
* Both headline statements keep the integrability side conditions as explicit hypotheses:
  without them the Bochner integrals are junk-valued `0` and the conclusion is false.

**Bibliographic comments.** Uniqueness of the (two-sided) Laplace transform on a strip goes
back to M. Lerch ("Sur un point de la théorie des fonctions génératrices d'Abel," *Acta
Math.* **27** (1903), 339–351); the systematic theory, including analyticity in the strip of
convergence and the resulting identity-theorem argument used here, is D. V. Widder's (*The
Laplace Transform*, Princeton University Press, 1941, Ch. II and VI).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.PointEstimation

/-- Tilted-transform identity: the Laplace transform of an exponential tilt is a ratio of
Laplace transforms of the base measure. Both sides are `0` in the degenerate case `μ = 0`. -/
private theorem integral_exp_tilted_mul
    -- USER-INPUT: the base measure; free choice
    {μ : Measure ℝ}
    -- USER-INPUT: the tilting parameter; free choice of the recentering point
    {t₀ : ℝ}
    -- USER-INPUT: the tilt is well defined at `t₀`; otherwise `Measure.tilted` is junk `0`
    (h₀ : Integrable (fun x => Real.exp (t₀ * x)) μ)
    -- USER-INPUT: the evaluation point of the tilted transform
    {t : ℝ}
    -- USER-INPUT: the base transform is finite at `t₀ + t`; otherwise the RHS is junk
    (ht : Integrable (fun x => Real.exp ((t₀ + t) * x)) μ) :
    ∫ x, Real.exp (t * x) ∂(μ.tilted fun x => t₀ * x)
      = (∫ x, Real.exp ((t₀ + t) * x) ∂μ) / ∫ x, Real.exp (t₀ * x) ∂μ := by
  sorry

/-- **Local `Set.EqOn` variant of `ProbabilityTheory.eqOn_complexMGF_of_mgf`.** Mathlib's
version requires the two real moment-generating functions to agree *globally*; here they are
only assumed to agree on an open nonempty set `S` contained in both integrability sets, which
is what the exponential-family applications supply. The conclusion is the equality of the two
`complexMGF`s on the vertical strip over the intersection of the two interiors. -/
private theorem eqOn_complexMGF_of_mgf_eqOn {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the two real random variables and their (possibly different) laws
    {X Y : Ω → ℝ} {μ μ' : Measure Ω}
    -- USER-INPUT: the comparison set; open and nonempty so that it accumulates in the strip
    {S : Set ℝ} (hS : IsOpen S) (hS' : S.Nonempty)
    -- USER-INPUT: `S` is inside the integrability set of `X`; makes `mgf X μ` honest on `S`
    (hX : S ⊆ integrableExpSet X μ)
    -- USER-INPUT: same for `Y`
    (hY : S ⊆ integrableExpSet Y μ')
    -- USER-INPUT: the two moment-generating functions agree on `S` (the local hypothesis)
    (hXY : Set.EqOn (mgf X μ) (mgf Y μ') S) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ')
      {z : ℂ | z.re ∈ interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ')} := by
  sorry

/-- **Laplace-transform uniqueness, local form.** Two finite measures on `ℝ` whose Laplace
transforms are finite and agree on a set `S` with an interior point coincide. -/
theorem ext_of_integral_exp_eqOn
    -- USER-INPUT: the two measures being compared; genuine external data
    {μ ν : Measure ℝ}
    -- USER-INPUT: both are finite; the conclusion is false for infinite measures with
    -- everywhere-infinite transforms, and `Measure.ext_of_charFun` needs finiteness
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    -- USER-INPUT: the set on which the two transforms are compared; free choice
    {S : Set ℝ}
    -- USER-INPUT: `S` has an interior point; supplies the analytic-continuation seed
    (hS : (interior S).Nonempty)
    -- USER-INPUT: finiteness of the transform of `μ` on `S`; else `∫` is junk-valued `0`
    (hμ : ∀ t ∈ S, Integrable (fun x => Real.exp (t * x)) μ)
    -- USER-INPUT: finiteness of the transform of `ν` on `S`
    (hν : ∀ t ∈ S, Integrable (fun x => Real.exp (t * x)) ν)
    -- USER-INPUT: the two Laplace transforms agree on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, Real.exp (t * x) ∂μ = ∫ x, Real.exp (t * x) ∂ν) :
    μ = ν := by
  sorry

/-- **Signed corollary.** If the `e^{tx}`-weighted integrals of a measurable `f` vanish for
every `t` in a set with an interior point, then `f` vanishes almost everywhere. This is the
analytic core of completeness for full-rank exponential families. -/
theorem ae_eq_zero_of_integral_exp_smul_eq_zero
    -- USER-INPUT: the reference measure; free choice
    {ν : Measure ℝ}
    -- USER-INPUT: σ-finiteness; needed to read an a.e. equality off equal `withDensity`s
    [SigmaFinite ν]
    -- USER-INPUT: the candidate function (an unbiased estimator of `0` in applications)
    {f : ℝ → ℝ} (hf : Measurable f)
    -- USER-INPUT: the parameter set; free choice
    {S : Set ℝ}
    -- USER-INPUT: `S` has an interior point; supplies the analytic-continuation seed
    (hS : (interior S).Nonempty)
    -- USER-INPUT: the weighted integrals exist on `S`; else `∫` is junk-valued `0`
    (hint : ∀ t ∈ S, Integrable (fun x => f x * Real.exp (t * x)) ν)
    -- USER-INPUT: the weighted integrals vanish on `S`; the substantive hypothesis
    (h : ∀ t ∈ S, ∫ x, f x * Real.exp (t * x) ∂ν = 0) :
    f =ᵐ[ν] 0 := by
  sorry

end StatLean.PointEstimation
