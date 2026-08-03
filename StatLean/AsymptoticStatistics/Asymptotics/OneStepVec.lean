import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec
import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec

/-!
# One-step estimator semiparametric efficiency — vector parameter

Vector-parameter (`θ ∈ ℝᵈ`) counterpart of
`AsymptoticStatistics.Asymptotics.OneStep`. Given a `√n`-rate consistent
preliminary estimator, the one-step estimator
`θ̂_n := θ̃_n + Î_n⁻¹ · (1/n) Σ_i ℓ̂_n(X_i, θ̃_n)` (with `Î_n⁻¹` a `d × d`
matrix correction) is asymptotically linear with vector influence
function `Ĩ⁻¹ ℓ̃` and asymptotically efficient under (25.55) + (25.56).

The field `asympLinear_25_57_vec` records the vector asymptotic-linear
premise consumed by the efficiency assembly.

Reference: vdV §25.5, thm:25.57 (vector form).

Headline declarations: `OneStepAssumptions_vec`,
`oneStep_semiparametricallyEfficient_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.OneStepVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- *Bundled assumptions for vdV thm:25.57 (one-step semiparametric
efficiency, vector parameter).*

Structure parameters: model identity (`S_θ`, `T_nuis`, `e`, `T`, `Dψ`) +
estimator triple (`preliminary`, `score_estimate_seq`,
`info_estimate_seq`) + the combined one-step estimator + vector
centering `θ₀`. The one-step formula `estimator_def` uses the matrix
inverse `Î_n⁻¹` of the (vector-valued) information estimate.

Reference: vdV §25.5, thm:25.57 (vector form). -/
structure OneStepAssumptions_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d))
    (preliminary : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (score_estimate_seq : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (info_estimate_seq : ∀ n, (Fin n → Ω) → Matrix (Fin d) (Fin d) ℝ)
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) where
  /-- vdV §25.4 (lem:25.25): `Ĩ` positive-definite. -/
  hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef
  /-- vdV §25.4 (lem:25.25): each `IF j ∈ T`. -/
  h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T
  /-- vdV §25.4 (lem:25.25): `Dψ`'s `j`-th coordinate acts as `⟪IF j, ·⟫`. -/
  h_Dψ : ∀ (j : Fin d) (g : T),
    (EuclideanSpace.proj j ∘L Dψ) g
      = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.5 (eq:25.58, vector form): the one-step estimator is the
  preliminary plus the matrix-corrected empirical mean
  `θ̂_n = θ̃_n + Î_n⁻¹ · (1/n) Σ_i ℓ̂_n(X_i, θ̃_n)`. -/
  estimator_def : ∀ n (X : Fin n → Ω),
    estimator n X
      = preliminary n X
        + (info_estimate_seq n X)⁻¹.mulVecLin
            ((n : ℝ)⁻¹ • (∑ i, score_estimate_seq n (X i) (preliminary n X)))
  /-- vdV §25.5 (eqs:25.55 + 25.56 + `√n`-rate + info consistency
  `Î_n →_P Ĩ`): the one-step estimator is asymptotically linear at `P`
  with vector influence tuple `IF` and centering `θ₀`. -/
  asympLinear_25_57_vec :
    AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) θ₀

/-- *vdV thm:25.57 — one-step semiparametric efficiency (vector
parameter).*

If the bundled `OneStepAssumptions_vec` holds and the vector centering
equals `ψ P`, then `estimator` is semiparametrically efficient at `P` for
the vector functional `ψ` relative to `T`.

Reference: vdV §25.5, thm:25.57 (vector form).

Proof template (mirroring the scalar):
* **Step A** — produce the vector EIF via `eif_from_efficientScore_vec`.
* **Step B** — unwrap `asympLinear_25_57_vec` modulo `ψ P = θ₀`.
* **Step C** — combine via
  `estimator_semiparametricallyEfficient_of_asympLinear_eif_vec`. -/
theorem oneStep_semiparametricallyEfficient_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {preliminary : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {score_estimate_seq :
      ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → Matrix (Fin d) (Fin d) ℝ}
    {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (h : OneStepAssumptions_vec P Θ S_θ T_nuis e T Dψ
            preliminary score_estimate_seq info_estimate_seq estimator θ₀)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction_vec Dψ
      (candidateVecEIF S_θ T_nuis e) :=
    eif_from_efficientScore_vec S_θ T_nuis e T Dψ h.hPD h.h_mem h.h_Dψ
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) (ψ P) := by
    rw [h_ψ]; exact h.asympLinear_25_57_vec
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

end AsymptoticStatistics.Asymptotics.OneStepVec
