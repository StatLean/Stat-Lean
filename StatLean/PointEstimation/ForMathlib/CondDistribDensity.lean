import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Conditional distributions of a jointly absolutely continuous law

For a joint law on `S × ℝ` given by a density `p` against `ν ⊗ volume`, the conditional
distribution of the second coordinate given the first is the normalized slice
`y ↦ p (t, y) / ∫ p (t, ·)`. This file records the three steps:

* `map_fst_withDensity_prod` — the first marginal has density `t ↦ ∫⁻ p (t, y) dy` (Tonelli);
* `lintegral_withDensity_prod` — integration against the joint law is iterated integration
  against `ν` of slice integrals weighted by `p`;
* `condDistrib_withDensity_prod_ae_eq` — Mathlib's `ProbabilityTheory.condDistrib` for
  `(Prod.snd ∣ Prod.fst)` is almost everywhere the normalized-slice measure.

**Reference.** Classical disintegration of an absolutely continuous joint law; original
sources in the bibliographic comments below.

**Proof formalization notes.**
* **No `Kernel` is defined here.** Packaging `t ↦ (∫⁻ p (t, ·))⁻¹ • volume.withDensity (p (t, ·))`
  as a `MeasureTheory.Kernel` would require discharging the kernel measurability obligation as
  part of the *definition*, which is exactly the work the file is meant to postpone. Instead
  the identification is stated pointwise, almost everywhere in `t`, against Mathlib's
  already-constructed `condDistrib`. Callers needing a kernel use `condDistrib` itself and
  rewrite with this lemma where a formula is required.
* **The joint density enters as an equation hypothesis** `hρ : ρ = (ν.prod volume).withDensity p`
  rather than by substituting the right-hand side into the statement. This keeps
  `IsFiniteMeasure ρ` (needed by `condDistrib`) as a hypothesis on the object the caller
  actually holds, and lets the lemma be applied to a `ρ` obtained as a pushforward or a
  restriction that is only *afterwards* shown to have this form.
* **Route for the third statement.** By `map_fst_withDensity_prod` the first marginal is
  `ν.withDensity (t ↦ ∫⁻ p (t, ·))`; by `lintegral_withDensity_prod` the composition-product
  of that marginal with the normalized-slice family reproduces `ρ`. A.e.-uniqueness of the
  disintegration of a finite measure on a product with standard Borel second factor
  (`MeasureTheory.Measure.eq_condKernel_of_measure_eq_compProd` and its `condDistrib`
  wrapper) then identifies the two kernels almost everywhere.
* **Normalization side conditions.** Slices with `∫⁻ p (t, ·) = 0` are null for the first
  marginal, and slices with `∫⁻ p (t, ·) = ⊤` would give a non-probability normalization; both
  are excluded by explicit a.e. hypotheses rather than by a junk-value convention, because the
  conclusion is an equality of measures where the junk branch is genuinely different.
* The second factor is fixed to `(ℝ, volume)`, which is what the location/scale conditional
  risk arguments consume; the same statements hold verbatim for any σ-finite measure on a
  standard Borel space, at the cost of one more variable.

**Bibliographic comments.** Conditional distributions were introduced by A. N. Kolmogorov
(*Grundbegriffe der Wahrscheinlichkeitsrechnung*, Springer, 1933, Ch. V); their existence as
regular conditional probabilities on standard Borel spaces, and the disintegration theorem
used for the a.e. identification, are due to J. L. Doob (*Stochastic Processes*, Wiley, 1953,
Ch. I §9).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {S : Type*} [MeasurableSpace S]

/-- The first marginal of a jointly absolutely continuous law has the slice-integral
density. -/
theorem map_fst_withDensity_prod
    -- USER-INPUT: the reference measure on the first factor; free choice
    {ν : Measure S}
    -- USER-INPUT: s-finiteness, the standing hypothesis for products and Tonelli
    [SFinite ν]
    -- USER-INPUT: the joint density and its measurability
    {p : S × ℝ → ℝ≥0∞} (hp : Measurable p) :
    ((ν.prod volume).withDensity p).map Prod.fst
      = ν.withDensity fun t => ∫⁻ y, p (t, y) ∂volume := by
  sorry

/-- Integration against a jointly absolutely continuous law, written as an iterated integral
of density-weighted slices. -/
theorem lintegral_withDensity_prod
    -- USER-INPUT: the reference measure on the first factor; free choice
    {ν : Measure S}
    -- USER-INPUT: s-finiteness, the standing hypothesis for products and Tonelli
    [SFinite ν]
    -- USER-INPUT: the joint density and its measurability
    {p : S × ℝ → ℝ≥0∞} (hp : Measurable p)
    -- USER-INPUT: the integrand and its measurability
    {f : S × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂((ν.prod volume).withDensity p)
      = ∫⁻ t, (∫⁻ y, f (t, y) * p (t, y) ∂volume) ∂ν := by
  sorry

/-- **Conditional distribution of a jointly absolutely continuous law.** The regular
conditional distribution of the second coordinate given the first is almost everywhere the
normalized slice of the joint density. -/
theorem condDistrib_withDensity_prod_ae_eq
    -- USER-INPUT: the first factor is standard Borel; needed for a.e. uniqueness of the
    -- disintegration
    [StandardBorelSpace S]
    -- USER-INPUT: the reference measure on the first factor; free choice
    {ν : Measure S}
    -- USER-INPUT: s-finiteness, the standing hypothesis for products and Tonelli
    [SFinite ν]
    -- USER-INPUT: the joint density and its measurability
    {p : S × ℝ → ℝ≥0∞} (hp : Measurable p)
    -- USER-INPUT: the joint law the caller actually holds
    {ρ : Measure (S × ℝ)}
    -- USER-INPUT: finiteness of the joint law; required by `condDistrib`
    [IsFiniteMeasure ρ]
    -- USER-INPUT: the joint law is the density `p` against `ν ⊗ volume`
    (hρ : ρ = (ν.prod volume).withDensity p)
    -- USER-INPUT: slice masses are finite a.e.; else the normalization is not a probability
    (hp_ne_top : ∀ᵐ t ∂ν, (∫⁻ y, p (t, y) ∂volume) ≠ ⊤)
    -- USER-INPUT: slice masses are nonzero a.e.; else the normalization is junk-valued
    (hp_ne_zero : ∀ᵐ t ∂ν, (∫⁻ y, p (t, y) ∂volume) ≠ 0) :
    ∀ᵐ t ∂(ρ.map Prod.fst),
      condDistrib Prod.snd Prod.fst ρ t
        = (∫⁻ y, p (t, y) ∂volume)⁻¹ • volume.withDensity fun y => p (t, y) := by
  sorry

end StatLean.PointEstimation
