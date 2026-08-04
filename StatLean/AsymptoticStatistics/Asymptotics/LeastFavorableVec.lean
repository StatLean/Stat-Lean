import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec
import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec
import StatLean.AsymptoticStatistics.Core.QMDPath

/-!
# MLE via approximate least-favorable submodel — vector parameter

Vector-parameter (`θ ∈ ℝᵈ`) counterpart of
`AsymptoticStatistics.Asymptotics.LeastFavorable`. vdV thm:25.77 states the efficient
information *matrix* `Ĩ` nonsingular, so the book-faithful statement is vector; this is
the assembly layer (bundle + headline), mirroring `Asymptotics.ZEstimatorVec`.

As in the scalar layer, the empirical-process content of eq:25.75 / eq:25.76 is *not*
formalized here: `asympLinear_25_77_vec` bundles the vector asymptotic-linear expansion.
Discharge from book primitives is `Asymptotics.Discharge.LeastFavorableVec`.

Reference: vdV §25.11, thm:25.77 (vector form); eq:25.75, eq:25.76.

Headline declarations: `ApproxLeastFavAssumptions_vec`,
`mle_semiparametricallyEfficient_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.LeastFavorableVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- Bundled assumptions for vdV thm:25.77 (MLE semiparametric efficiency via an
approximately-least-favorable submodel), **vector parameter**.

Vector counterpart of `ApproxLeastFavAssumptions`: scalar direction `v : Θ` and scalar
information `Ĩ` become directions `e : Fin d → Θ` and the efficient information *matrix*;
the scalar submodel becomes one per direction `submodel_path : Fin d → Θ → QMDPath P`.

Reference: vdV §25.11, thm:25.77 (vector form); eq:25.75. -/
structure ApproxLeastFavAssumptions_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d))
    (submodel_path : Fin d → Θ → QMDPath P)
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) where
  /-- vdV §25.4 (lem:25.25): efficient information matrix positive-definite. -/
  hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef
  /-- vdV §25.4 (lem:25.25): each component of the vector EIF lies in `T`. -/
  h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T
  /-- vdV §25.4 (lem:25.25): `Dψ`'s `j`-th coordinate acts as `⟪IF j, ·⟫`. -/
  h_Dψ : ∀ (j : Fin d) (g : T),
    (EuclideanSpace.proj j ∘L Dψ) g
      = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.11 (eq:25.75 at `s = 0`, per direction): each submodel's score at the
  origin matches the efficient score in that direction. This records the least-favorable
  submodel condition in the book-facing bundle interface; neither the final assembly proof
  nor the separate native vector discharge consumes this field directly. -/
  submodel_score_at_zero : ∀ j,
    (submodel_path j 0).score = efficientScore S_θ T_nuis (e j)
  /-- vdV §25.11 (eqs:25.75 + 25.76 + MLE stationarity): the MLE is asymptotically
  linear at `P` with vector influence tuple `candidateVecEIF` and centering `θ₀`.
  This bundle separately records the least-favorable score identity in
  `submodel_score_at_zero`. The native vector discharge in
  `Asymptotics/Discharge/LeastFavorableVec.lean` consumes a supplied
  `ZEstimatorTaylorCoreNative_vec` and does not use that identity field directly. -/
  asympLinear_25_77_vec :
    AsymptoticallyLinearAt_vec estimator P (candidateVecEIF S_θ T_nuis e) θ₀

/-- vdV thm:25.77 (vector form) — MLE semiparametric efficiency via approximate
least-favorable submodel. If the bundle holds and `ψ P = θ₀`, then `estimator` is
semiparametrically efficient at `P` for `ψ` relative to `T`.

Proof (mirrors `zEstimator_semiparametricallyEfficient_vec`): vector EIF via
`eif_from_efficientScore_vec`; bundled vector AL modulo `ψ P = θ₀`; combine via
`estimator_semiparametricallyEfficient_of_asympLinear_eif_vec`.

Reference: vdV §25.11, thm:25.77 (vector form). -/
theorem mle_semiparametricallyEfficient_vec
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {submodel_path : Fin d → Θ → QMDPath P}
    {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
    {θ₀ : EuclideanSpace ℝ (Fin d)}
    (h : ApproxLeastFavAssumptions_vec P Θ S_θ T_nuis e T Dψ
            submodel_path estimator θ₀)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction_vec Dψ (candidateVecEIF S_θ T_nuis e) :=
    eif_from_efficientScore_vec S_θ T_nuis e T Dψ h.hPD h.h_mem h.h_Dψ
  have hAL : AsymptoticallyLinearAt_vec estimator P
      (candidateVecEIF S_θ T_nuis e) (ψ P) := by
    rw [h_ψ]; exact h.asympLinear_25_77_vec
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF hAL

end AsymptoticStatistics.Asymptotics.LeastFavorableVec
