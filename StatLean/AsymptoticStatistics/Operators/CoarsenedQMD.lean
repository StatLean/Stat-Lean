import StatLean.AsymptoticStatistics.Core.QMDPath
import StatLean.AsymptoticStatistics.Operators.InformationLoss
import StatLean.AsymptoticStatistics.Operators.CoarsenedQMDLimit

/-!
# Coarsening a QMD path through the observation map (vdV lem:25.34-I)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3,
lem:25.34(I), book p.374-375. Van der Vaart states the preservation result and
refers its proof to [139, pp.188-193].

Given a full-data QMD path `γ : QMDPath P_full` and a measurable coarsening
`M : Ω_full → Ω_obs`, the pushed-forward curve `t ↦ (γ.curve t).map M` is again a
QMD path at `P_full.map M`, whose score is the information-loss image
`Π γ.score = E(γ.score | M⁻¹σ_obs)` of the full-data score (lem:25.34-I: taking a
conditional expectation of a QMD score produces the QMD score of the induced
coarsened path).

`QMDPath.coarsen` packages this. Its curve, probability, absolute-continuity,
and curve-at-zero fields follow directly; the **score field is `Π γ.score`**,
and its `qmd_limit` field (the score-preservation statement that
part vdV outsources to [139]) is established by `coarsen_qmd_limit`
(`Operators/CoarsenedQMDLimit.lean`).

Headline declaration: `QMDPath.coarsen`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Core.QMDPath

open AsymptoticStatistics.Operators.InformationLoss

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]

/-- *Coarsening of a QMD path through the observation map* (vdV lem:25.34-I,
book p.374-375, whose proof is referred to [139, pp.188-193]).

Pushes a full-data QMD path `γ : QMDPath P_full` forward through a measurable
coarsening `M`, yielding a QMD path at `P_full.map M` with:
  * `curve t := (γ.curve t).map M` (the induced observed-data law),
  * `dominating := γ.dominating.map M`,
  * `score := informationLossOperator hM P_full γ.score = Π γ.score` (the
    conditional-expectation image of the full-data score — lem:25.34-I).

The remaining structure fields are obtained as follows.
  * `dominating_sigmaFinite` — discharged from the explicit
    `[SigmaFinite (γ.dominating.map M)]` regularity hypothesis (pushforward of a
    σ-finite measure need not be σ-finite, so it must be supplied as a regularity
    input on the observed space).
  * `qmd_limit` — the score-preservation statement of lem:25.34-I, for whose
    proof van der Vaart refers to [139, pp.188-193], follows from
    `coarsen_qmd_limit`. -/
noncomputable def QMDPath.coarsen {M : Ω_full → Ω_obs} (hM : Measurable M)
    {P_full : Measure Ω_full} [IsProbabilityMeasure P_full]
    (γ : QMDPath P_full)
    -- Regularity: σ-finiteness of the pushed-forward dominating
    -- measure on the observed space; not forced by the setup (pushforward of a
    -- σ-finite measure need not be σ-finite), so supplied explicitly.
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
    -- The score-preservation result lem:25.34-I, which vdV outsources to
    -- [139, pp.188-193], follows
    -- by `coarsen_qmd_limit` via the conditional-projection λ=1 domination route
    -- (the pulled-back √-density residual splits into two `o(t)` L²(μ) brackets,
    -- bounded by conditional Cauchy–Schwarz on the QMD remainder plus a ρ-ratio
    -- DCT argument).
    qmd_limit := coarsen_qmd_limit hM γ }

end AsymptoticStatistics.Core.QMDPath
