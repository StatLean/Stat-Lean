import StatLean.AsymptoticStatistics.ClassicalZEstimator.RootExistence
import StatLean.AsymptoticStatistics.ClassicalZEstimator.AsymptoticNormality

/-!
# Existence and asymptotic normality of a classical Z-estimator root

This module combines the measurable-selection-free root existence and consistency
conclusion of van der Vaart Theorem 5.42 with the outer asymptotic normality form of Theorem
5.41. No measurability of the selected root sequence is required.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix

namespace AsymptoticStatistics.ClassicalZEstimator

open AsymptoticStatistics.EmpiricalProcess

/-- **Classical Z-estimator existence and outer asymptotic normality (vdV 5.42 + 5.41).**
Under the classical smoothness conditions there is, with inner probability tending to one, a
root of the estimating equation, and one can select a consistent root sequence satisfying the
classical linear representation and the corresponding outer Gaussian limit. -/
theorem classical_zEstimator_exists_normal_root
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    TendstoInnerProbOne μ (fun n => {ξ | ∃ θ ∈ Θ, ∀ j,
        empiricalAvg (ψ θ j) n (fun i : Fin n => X i.val ξ) = 0})
    ∧ ∃ θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k),
        TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
            empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
              (fun i : Fin n => X i.val ξ) = 0})
        ∧ TendstoInProbZero (fun _ : ℕ => μ)
            (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        ∧ TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
            Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
              + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
                  (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
        ∧ WeakConvergesOuter (fun _ : ℕ => μ)
            (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
            (multivariateGaussian 0
              ((Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ)) := by
  obtain ⟨hexists, θ_hat, hroot, hcons⟩ :=
    classical_zEstimator_root_exists_consistent P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
      hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom μ X hX_meas hX_indep hX_id
      hX_law
  refine ⟨hexists, θ_hat, hroot, hcons, ?_⟩
  exact classical_zEstimator_normality_outer P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
    hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom θ_hat μ X hX_meas hX_indep
    hX_id hX_law hroot hcons

end AsymptoticStatistics.ClassicalZEstimator
