import StatLean.AsymptoticStatistics.StrictModel.EfficientScore
import StatLean.AsymptoticStatistics.Core.EfficiencyOperational
import StatLean.AsymptoticStatistics.Core.QMDPath

/-!
# MLE via approximate least-favorable submodel

A one-parameter submodel `submodel_path : Θ → QMDPath P` is constructed so that its
score at `s = 0` matches the efficient score `ℓ̃ = efficientScore S_θ T_nuis v` of the
full model. The MLE `θ̂_n = argmax_s P_n log p_{s, η̂_s}` along this submodel inherits
asymptotic linearity with influence function `(1/Ĩ) ℓ̃` and is asymptotically efficient.

The submodel is *approximate* in vdV's sense: at `s = 0` the score matches the efficient
score of the full semiparametric model exactly; for `s ≠ 0` the submodel need only be QMD
with score sufficiently close to a smooth-in-`s` family, with the slack absorbed by the
eq:25.76 Donsker / no-bias condition.

Scope is restricted to a scalar parameter / 1-dim score direction (θ ∈ ℝ via the Hilbert
direction `v : Θ`); vdV's full thm:25.77 has an infinite-dim nuisance with a
least-favorable direction in a Banach space.

Reference: vdV §25.7 — eq:25.75 (least-favorable score identity), eq:25.76 (Donsker /
no-bias condition along the least-favorable submodel), thm:25.77 (MLE semiparametric
efficiency).

Headline declarations: `ApproxLeastFavAssumptions`, `mle_semiparametricallyEfficient`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.LeastFavorable

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Bundled assumptions for vdV thm:25.77 (MLE semiparametric efficiency via approximate
least-favorable submodel).

Structure parameters: model identity (`S_θ`, `T_nuis`, `v`, `T`, `dψ`) + the parametric
submodel `submodel_path : Θ → QMDPath P` + MLE sequence `estimator` + centering `θ₀`.
Structure body: EIF hypotheses + the LFM score identity + the empirical-process
consequence (`asympLinear_25_77`).

Reference: vdV §25.7, eqs:25.75, 25.76, thm:25.77.

Edge behavior:
* `efficientInformation = 0` ⇒ `hI_pos` fails ⇒ uninhabited.
* `submodel_path` always lives in `QMDPath P`, so QMD regularity is built into the type;
  no separate field needed.
* The LFM identity at the *origin* of the parameter space (i.e. at `submodel_path 0`) is
  exact; for `s ≠ 0` the submodel can drift, with the drift absorbed in
  `asympLinear_25_77`. This matches vdV's "approximate" qualifier on §25.7. -/
structure ApproxLeastFavAssumptions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ)
    (submodel_path : Θ → QMDPath P)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ) where
  /-- vdV §25.4 (lem:25.25): the candidate EIF `(1 / Ĩ) • ℓ̃` lies in the target tangent
  space `T`. -/
  h_mem :
    (1 / efficientInformation S_θ T_nuis v)
      • efficientScore S_θ T_nuis v ∈ T
  /-- vdV §25.4 (lem:25.25): `dψ` acts on `T` as `(1 / Ĩ) ⟪ℓ̃, ·⟫`. -/
  h_dψ : ∀ g : T,
    dψ g
      = (1 / efficientInformation S_θ T_nuis v)
          * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.4 (lem:25.25): efficient information is positive at `v`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.7 (eq:25.75 at `s = 0`): the submodel's score at the origin matches the
  efficient score of the full semiparametric model. This is the *least-favorable* property
  in vdV §25.7: among parametric paths inside the model, the chosen `submodel_path` is one
  whose score is `ℓ̃`.

  vdV's "approximate" qualifier permits `s ≠ 0` perturbations: those drifts are absorbed
  in the empirical-process bundle below; the origin score must match exactly. -/
  submodel_score_at_zero :
    (submodel_path 0).score = efficientScore S_θ T_nuis v
  /-- vdV §25.7 (eq:25.76 + MLE first-order condition along the LFM):

  the MLE `estimator` is asymptotically linear at `P` with influence function `(1 / Ĩ) • ℓ̃`
  and centering `θ₀`. Concrete model files prove this from the MLE's first-order condition
  along `submodel_path` together with eq:25.76 Donsker / no-bias machinery applied to the
  LFM derivative. -/
  asympLinear_25_77 :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v)
      θ₀

/-- vdV §25.7 thm:25.77 — MLE semiparametric efficiency via approximate least-favorable
submodel.

If the bundled `ApproxLeastFavAssumptions` holds for the model triple `(S_θ, T_nuis, v)`,
target tangent space `T`, derivative `dψ`, parametric submodel `submodel_path`, MLE
sequence `estimator`, and centering `θ₀ = ψ P`, then `estimator` is semiparametrically
efficient at `P` for the parameter functional `ψ` relative to `T`.

Reference: vdV §25.7, thm:25.77.

Proof template (shared with `ZEstimator`, `OneStep`):
* **Step A** — produce the EIF via `eif_from_efficientScore`.
* **Step B** — unwrap `asympLinear_25_77` modulo `ψ P = θ₀`.
* **Step C** — combine via `estimator_semiparametricallyEfficient_of_asympLinear_eif`.

The LFM score identity (eq:25.75 at `s = 0`) is bundled as `submodel_score_at_zero` and is
not used directly in this proof: it shapes `asympLinear_25_77` for downstream consumers. -/
theorem mle_semiparametricallyEfficient
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {submodel_path : Θ → QMDPath P}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : ApproxLeastFavAssumptions P Θ S_θ T_nuis v T dψ
            submodel_path estimator θ₀)
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) :=
    eif_from_efficientScore S_θ T_nuis v T h.h_mem dψ h.h_dψ
  have hAL : AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) (ψ P) := by
    rw [h_ψ]
    exact h.asympLinear_25_77
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF hAL

end AsymptoticStatistics.Asymptotics.LeastFavorable
