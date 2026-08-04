import StatLean.StatisticalModels.Model.Defs
import StatLean.PointEstimation.Model.Defs
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Adapter: dominated families ↔ the density carrier `ParametricFamily`

Interconversion between this area's measure-level dominated models
(`IsDominatedFamily P μ`, `Model.Defs`) and the library's density-level carrier
`AsymptoticStatistics.ParametricFamily` + `IsPDFOf` (via
`AsymptoticStatistics.ParametricFamily.toMeasure`, defined in
`StatLean.PointEstimation.Model.Defs`):

* density → measure: `toMeasure` lands in probability measures (`isProbabilityMeasure_toMeasure`)
  and is dominated (`isDominatedFamily_toMeasure`);
* measure → density: `ofDominated` recovers a `ParametricFamily` from a dominated family via
  Radon–Nikodym derivatives, with the round trip `toMeasure_ofDominated`.

The iid agreement `iid (M.toMeasure μ) n = AsymptoticStatistics.productMeasure M μ · n` holds
definitionally (both sides are `Measure.pi` of `toMeasure`) but is deliberately **not** stated
here: naming `productMeasure` would import the heavy LAN assembly module
(`LocalAsymptoticNormality.AsymptoticRepresentation`); the one-line agreement lemma is a
documented laptop follow-up in that file, not an import here.

**Reference.** Dominated families and their density representations: P. R. Halmos and
L. J. Savage, "Application of the Radon–Nikodym theorem to the theory of sufficient
statistics," *Ann. Math. Statist.* **20** (1949), 225–241; TPE2 §1.4 (verify §).

**Proof formalization notes.** `isProbabilityMeasure_toMeasure` hoists the inline computation
already performed at `LocalAsymptoticNormality/AsymptoticRepresentation.lean` (~line 100)
(`withDensity`-mass via `ENNReal.ofReal` of the normalization integral) into a named reusable
lemma — hoisted, not duplicated: that file can later rewrite through this one. `ofDominated`
takes real-valued densities `(∂P θ/∂μ).toReal`; the round trip needs σ-finiteness of the
members (LEAN-ONLY, satisfied by probability models) so that
`withDensity_rnDeriv_eq`-style reconstruction applies.

**Bibliographic comments.** Radon–Nikodym reconstruction of dominated families is the
Halmos–Savage device; the `toReal`/`ofReal` round trip is Lean-side bookkeeping with no book
counterpart.
-/

open MeasureTheory

namespace StatLean.StatisticalModels

variable {Θ : Type*} {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The measure family of a PDF family consists of probability measures. -/
theorem isProbabilityMeasure_toMeasure (M : AsymptoticStatistics.ParametricFamily 𝓧 Θ)
    {μ : Measure 𝓧}
    -- USER-INPUT: the densities are μ-PDFs (normalized, integrable); TPE2 §1.4
    (hPDF : AsymptoticStatistics.IsPDFOf M μ) (θ : Θ) :
    IsProbabilityMeasure (M.toMeasure μ θ) := by
  sorry

/-- The measure family of a density family is dominated by the reference measure. -/
theorem isDominatedFamily_toMeasure (M : AsymptoticStatistics.ParametricFamily 𝓧 Θ)
    (μ : Measure 𝓧) : IsDominatedFamily (M.toMeasure μ) μ := by
  sorry

/-- Recover a density carrier from a dominated family via Radon–Nikodym derivatives:
`density θ = (∂(P θ)/∂μ).toReal`. -/
noncomputable def ofDominated (P : Θ → Measure 𝓧) (μ : Measure 𝓧) :
    AsymptoticStatistics.ParametricFamily 𝓧 Θ where
  density θ x := ((P θ).rnDeriv μ x).toReal
  density_meas θ := by sorry
  density_nonneg θ x := by sorry

/-- Round trip: for a dominated family of σ-finite members over a σ-finite reference
measure, rebuilding the measures from the Radon–Nikodym densities recovers the family. -/
theorem toMeasure_ofDominated (P : Θ → Measure 𝓧) (μ : Measure 𝓧)
    -- USER-INPUT: domination; Halmos–Savage 1949
    (h : IsDominatedFamily P μ)
    -- LEAN-ONLY: σ-finiteness for Radon–Nikodym; standard regularity
    [SigmaFinite μ] [∀ θ, SigmaFinite (P θ)] (θ : Θ) :
    (ofDominated P μ).toMeasure μ θ = P θ := by
  sorry

end StatLean.StatisticalModels
