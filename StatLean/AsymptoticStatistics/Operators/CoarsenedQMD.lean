import StatLean.AsymptoticStatistics.Core.QMDPath
import StatLean.AsymptoticStatistics.Operators.InformationLoss
import StatLean.AsymptoticStatistics.Operators.CoarsenedQMDLimit

/-!
# Coarsening a QMD path through the observation map (vdV lem:25.34-I)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.2,
lem:25.34(I), book p.375. **The book defers the proof of this preservation
to reference [139, pp.188-193].**

Given a full-data QMD path `γ : QMDPath P_full` and a measurable coarsening
`M : Ω_full → Ω_obs`, the pushed-forward curve `t ↦ (γ.curve t).map M` is again a
QMD path at `P_full.map M`, whose score is the information-loss image
`Π γ.score = E(γ.score | M⁻¹σ_obs)` of the full-data score (lem:25.34-I: taking a
conditional expectation of a QMD score produces the QMD score of the induced
coarsened path).

`QMDPath.coarsen` packages this after internally rebasing to an equivalent finite
dominator. Its routine fields (curve/probability/absolute
continuity/curve-at-zero) are discharged directly; the **score field is
`Π γ.score`**, and the `qmd_limit` field (the score-preservation statement that
part vdV outsources to [139]) follows from `coarsen_qmd_limit`
(`Operators/CoarsenedQMDLimit.lean`), which directly proves the result that vdV
defers to [139].

Headline declaration: `QMDPath.coarsen`. Compatibility core:
`QMDPath.coarsenWithMappedSigmaFinite`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Core.QMDPath

open AsymptoticStatistics.Operators.InformationLoss

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]

/-- *Low-level coarsening core with an explicit mapped sigma-finiteness instance.*

Compatibility form of vdV Lemma 25.34-I (book p.375; score preservation is
book-deferred to [139]). The faithful public entry is `QMDPath.coarsen` below.

Pushes a full-data QMD path `γ : QMDPath P_full` forward through a measurable
coarsening `M`, yielding a QMD path at `P_full.map M` with:
  * `curve t := (γ.curve t).map M` (the induced observed-data law),
  * `dominating := γ.dominating.map M`,
  * `score := informationLossOperator hM P_full γ.score = Π γ.score` (the
    conditional-expectation image of the full-data score — lem:25.34-I).

The routine fields are discharged directly.
  * `dominating_sigmaFinite` — discharged from the explicit low-level
    `[SigmaFinite (γ.dominating.map M)]` compatibility instance. The public entry
    derives this internally after rebasing to a finite equivalent dominator.
  * `qmd_limit` — the genuine score-preservation lem:25.34-I, which van der Vaart
    outsources to [139, pp.188-193]; here proven directly via `coarsen_qmd_limit`. -/
noncomputable def QMDPath.coarsenWithMappedSigmaFinite {M : Ω_full → Ω_obs}
    (hM : Measurable M)
    {P_full : Measure Ω_full} [IsProbabilityMeasure P_full]
    (γ : QMDPath P_full)
    -- Sigma-finiteness of the pushed-forward dominating measure is required by
    -- this compatibility constructor; a pushforward of a sigma-finite measure
    -- need not itself be sigma-finite.
    [hσ : SigmaFinite ((γ.dominating).map M)] :
    letI : IsProbabilityMeasure (P_full.map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    QMDPath (P_full.map M) :=
  letI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  { curve := fun t => (γ.curve t).map M
    curve_at_zero := by simp only [γ.curve_at_zero]
    curve_isProbability := fun t => by
      haveI := γ.curve_isProbability t
      exact Measure.isProbabilityMeasure_map hM.aemeasurable
    dominating := γ.dominating.map M
    curve_absContinuous := fun t => (γ.curve_absContinuous t).map hM
    -- Discharged from the explicit `[SigmaFinite (γ.dominating.map M)]` regularity
    -- hypothesis (pushforward of a σ-finite measure need not be σ-finite).
    dominating_sigmaFinite := hσ
    score := informationLossOperator hM P_full γ.score
    -- The score-preservation statement in Lemma 25.34-I, which vdV refers to
    -- [139, pp.188-193], follows from `coarsen_qmd_limit` via conditional-projection
    -- domination
    -- (the pulled-back √-density residual splits into two `o(t)` L²(μ) brackets,
    -- bounded by conditional Cauchy–Schwarz on the QMD remainder plus a ρ-ratio
    -- DCT argument).
    qmd_limit := coarsen_qmd_limit_withMappedSigmaFinite hM γ }

/-- *Coarsening of a QMD path through the observation map* (vdV Lemma 25.34-I,
book p.375), with no mapped-sigma-finiteness obligation on the caller.

The implementation first replaces `γ.dominating` by the equivalent finite
dominator supplied by `finiteDominatorRepresentation`.  Its pushforward through
`M` is finite, hence sigma-finite, so the low-level compatibility constructor
`coarsenWithMappedSigmaFinite` applies internally.  The adapter preserves the
curve and score, and therefore the resulting observed path has curve
`t ↦ (γ.curve t).map M` and score
`informationLossOperator hM P_full γ.score`.

This is the faithful public entry: the measurable coarsening map and the QMD path
are the only caller-supplied data. -/
noncomputable def QMDPath.coarsen {M : Ω_full → Ω_obs} (hM : Measurable M)
    {P_full : Measure Ω_full} [IsProbabilityMeasure P_full]
    (γ : QMDPath P_full) :
    letI : IsProbabilityMeasure (P_full.map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    QMDPath (P_full.map M) := by
  let γfin := (finiteDominatorRepresentation γ).1
  have hcurve : γfin.curve = γ.curve := (finiteDominatorRepresentation γ).2.1
  have hdom : γfin.dominating = γ.dominating.toFinite :=
    (finiteDominatorRepresentation γ).2.2.1
  have hscore : γfin.score = γ.score := (finiteDominatorRepresentation γ).2.2.2
  haveI : SigmaFinite (γfin.dominating.map M) := by
    rw [hdom]
    infer_instance
  letI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  let γmapped := QMDPath.coarsenWithMappedSigmaFinite hM γfin
  exact
    { curve := γmapped.curve
      curve_at_zero := γmapped.curve_at_zero
      curve_isProbability := γmapped.curve_isProbability
      dominating := γmapped.dominating
      curve_absContinuous := γmapped.curve_absContinuous
      dominating_sigmaFinite := γmapped.dominating_sigmaFinite
      score := γmapped.score
      qmd_limit := by
        simpa only [γmapped, QMDPath.coarsenWithMappedSigmaFinite, hcurve, hdom, hscore]
          using coarsen_qmd_limit hM γ }

end AsymptoticStatistics.Core.QMDPath
