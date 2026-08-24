import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

/-!
# One-step estimator semiparametric efficiency (vector θ) — native discharge

Vector-parameter (`θ ∈ ℝᵈ`) discharge layer for the one-step estimator, providing the
discoverable vdV thm:25.57 (vector form) headline.

## Native route (no diagonal-only coordinatewise identification)

This module re-exports the native vector discharge through
`ZEstimatorTaylorCoreNative_vec` and does not require the diagonal-only coordinatewise
identity `(1/Ĩ_{e j})•ℓ̃(e j) = candidateVecEIF j`. The imported native theorem handles the
full matrix coupling for arbitrary positive-definite efficient information.

The one-step estimator solves the vector estimating equation `√n·𝕡_n ℓ̃_{θ̂_n} = o_P` up to
one Newton step, represented here by the vector/matrix primitive bundle
`ZEstimatorTaylorCoreNative_vec` (`hPD`, the vector estimating equation `score_eq_vec`, the
matrix Bartlett identity `matrix_bartlett`, the matrix DQM-Taylor remainder `matrix_taylor`).
The native discharge `ZEstimatorVecNative.mle_asympLinear_of_nativeTaylorCore_vec` then
gives its asymptotic linearity directly, with influence `Ĩ⁻¹ℓ̃ = candidateVecEIF` **by
construction** (arbitrary, non-diagonal `Ĩ`) and no coordinatewise identification.

Reference: vdV §25.5, thm:25.57 (vector form). Headline declarations:
`oneStep_asympLinear_native_vec`, `oneStep_semiparametricallyEfficient_native_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.OneStepVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

variable {Ω : Type} [MeasurableSpace Ω]
variable {d : ℕ}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {e : Fin d → Θ}
variable {estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → EuclideanSpace ℝ (Fin d))}
variable {score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P)}
variable {θ₀ : EuclideanSpace ℝ (Fin d)}

/-- vdV thm:25.57 (vector form) — asymptotic linearity of the one-step estimator, native
discharge. Because the one-step estimator solves the vector estimating equation
(`score_eq_vec` of the native bundle), the book-faithful native discharge
`ZEstimatorVecNative.mle_asympLinear_of_nativeTaylorCore_vec` makes it asymptotically
linear at `P` with influence tuple `candidateVecEIF S_θ T_nuis e` and vector centering `θ₀`.
Carries no diagonal-only coordinatewise identification (the matrix coupling is handled inside
the native master identity). -/
theorem oneStep_asympLinear_native_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    AsymptoticallyLinearAt_vec estimator P (candidateVecEIF S_θ T_nuis e) θ₀ :=
  mle_asympLinear_of_nativeTaylorCore_vec h

/-- vdV thm:25.57 (vector form) — semiparametric-efficiency headline of the one-step
estimator, native discharge. From
`ZEstimatorTaylorCoreNative_vec` (solved estimating equation etc.) plus the EIF-construction
inputs (`h_mem`, `h_Dψ`) and `ψ P = θ₀`, the one-step estimator is asymptotically efficient
at `P` relative to the tangent space `T` for the vector functional `ψ`. Re-export of
`ZEstimatorVecNative.mle_semiparametricallyEfficient_of_nativeTaylorCore_vec`; carries
no diagonal-only coordinatewise identification. -/
theorem oneStep_semiparametricallyEfficient_native_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T :=
  mle_semiparametricallyEfficient_of_nativeTaylorCore_vec h h_mem h_Dψ h_ψ

end AsymptoticStatistics.Asymptotics.Discharge.OneStepVec
