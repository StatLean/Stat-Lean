import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorVecNative

/-!
# MLE via approximate least-favorable submodel — vector discharge (native, book-faithful)

Vector counterpart of `Asymptotics.Discharge.LeastFavorable`, providing the discoverable
vdV thm:25.77 (vector form) headline for the semiparametric MLE.

## Native route (no diagonal-only coordinatewise identification)

This module exposes the native vector interface `ZEstimatorTaylorCoreNative_vec` and does
not require the diagonal-only coordinatewise identity
`(1/Ĩ_{e j})•ℓ̃(e j) = candidateVecEIF j`. The imported native discharge handles the full
matrix coupling for arbitrary positive-definite efficient information.

The headline uses the **native** multivariate discharge
`ZEstimatorVecNative.mle_semiparametricallyEfficient_of_leastFavorable_native_vec`, which
derives the vector residual directly through the `d × d` master identity
`√n·Ĩ·(θ̂−θ₀) = 𝔾ₙℓ̃ + o_P` and then applies `Ĩ⁻¹`, so the influence is
`Ĩ⁻¹ℓ̃ = candidateVecEIF` **by construction** — valid for arbitrary (non-diagonal) `Ĩ`, with
no coordinatewise identification. Its hypothesis is the vector/matrix primitive bundle
`ZEstimatorTaylorCoreNative_vec` (`hPD`, the vector estimating equation `score_eq_vec`,
the matrix Bartlett identity `matrix_bartlett`, the matrix DQM-Taylor remainder
`matrix_taylor`).

Reference: vdV §25.11, thm:25.77 (vector form) — "Theorem 25.54, with `ℓ̃` replaced by
`κ̃`" (p.409). Headline declarations: `mle_asympLinear_of_leastFavorable_vec`,
`mle_semiparametricallyEfficient_of_leastFavorable_vec`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.LeastFavorableVec

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

/-- vdV thm:25.77 (vector form) — asymptotic linearity of the semiparametric MLE, native
discharge. Re-export of the book-faithful native discharge
`ZEstimatorVecNative.mle_asympLinear_of_leastFavorable_native_vec`: from
`ZEstimatorTaylorCoreNative_vec`, the MLE is asymptotically linear at
`P` with influence tuple `candidateVecEIF S_θ T_nuis e` and vector centering `θ₀`. Carries
no diagonal-only coordinatewise identification (the matrix coupling is handled inside the
native master identity). -/
theorem mle_asympLinear_of_leastFavorable_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀) :
    AsymptoticallyLinearAt_vec estimator P (candidateVecEIF S_θ T_nuis e) θ₀ :=
  mle_asympLinear_of_leastFavorable_native_vec h

/-- vdV thm:25.77 (vector form) — semiparametric-efficiency headline of the MLE via an
approximately-least-favorable submodel, native discharge. Re-export of the book-faithful
native discharge
`ZEstimatorVecNative.mle_semiparametricallyEfficient_of_leastFavorable_native_vec`: from
`ZEstimatorTaylorCoreNative_vec` plus the EIF-construction inputs
(`h_mem`, `h_Dψ`) and `ψ P = θ₀`, the MLE is asymptotically efficient at `P` relative to the
tangent space `T` for the vector functional `ψ`. Carries no diagonal-only coordinatewise
identification. -/
theorem mle_semiparametricallyEfficient_of_leastFavorable_vec
    (h : ZEstimatorTaylorCoreNative_vec P Θ S_θ T_nuis e estimator
            score_func_seq score_l_dot θ₀)
    {T : Submodule ℝ ↥(L2ZeroMean P)} {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt_vec estimator ψ P T :=
  mle_semiparametricallyEfficient_of_leastFavorable_native_vec h h_mem h_Dψ h_ψ

end AsymptoticStatistics.Asymptotics.Discharge.LeastFavorableVec
