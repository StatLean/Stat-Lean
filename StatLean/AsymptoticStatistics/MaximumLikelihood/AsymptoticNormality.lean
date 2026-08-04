import StatLean.AsymptoticStatistics.DQM.LogDensityPopulationTaylor
import StatLean.AsymptoticStatistics.MaximumLikelihood.Consistency
import StatLean.AsymptoticStatistics.MaximumLikelihood.FisherAdapters
import StatLean.AsymptoticStatistics.MaximumLikelihood.ProductComparisons
import StatLean.AsymptoticStatistics.MEstimator.DifferentiabilityInProbability
import StatLean.AsymptoticStatistics.MEstimator.AsymptoticNormality

/-!
# Maximum-likelihood asymptotic normality

Statement-and-assembly layer for van der Vaart, *Asymptotic Statistics*,
Theorem 5.39 (pp. 65--66).  The headline derives consistency through the
stabilized Kullback--Leibler/T4 route, derives the score and Taylor inputs from
DQM, and then applies the fixed-maximizer M-estimator interface.  It does not
assume consistency, pointwise log-density derivatives, strict positivity, or
provider equalities.
-/

namespace AsymptoticStatistics.MaximumLikelihood

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

set_option maxHeartbeats 800000 in
-- The typeclass-heavy assembly instantiates the full T8 empirical-process interface.
/-- **Maximum-likelihood asymptotic normality (vdV Theorem 5.39).**

For a DQM model with a measurable local square-integrable log-Lipschitz
envelope, positive-definite Fisher information, and an exact empirical MLE,
the estimator has the inverse-Fisher asymptotic linear representation and is
asymptotically `N(0, I⁻¹)`.  Consistency and every score/Fisher/Taylor adapter
are derived by the preceding results rather than assumed by this theorem. -/
theorem mle_asymptotic_normality
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : ParametricFamily Ω (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: the model is a family of probability densities w.r.t. μ; vdV §5.5
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: identifiability, P_θ = P_{θ₀} → θ = θ₀; vdV Lem 5.35 (used to
    -- derive the consistency required by Thm 5.39)
    (hident : ∀ θ,
      parametricMeasure M μ θ = parametricMeasure M μ θ₀ → θ = θ₀)
    -- USER-INPUT: upper semicontinuity of the population criterion (Wald-type
    -- regularity for the internal consistency step); vdV §5.2
    (husc : UpperSemicontinuous (stabilizedPopulationCriterion M μ θ₀))
    -- USER-INPUT: a compact superlevel set below the maximum (compactness caveat
    -- for the internal consistency step); vdV §5.2
    (hcompact : ∃ c : ℝ,
      c < stabilizedPopulationCriterion M μ θ₀ θ₀ ∧
        IsCompact {θ | c ≤ stabilizedPopulationCriterion M μ θ₀ θ})
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : ℕ → Ξ → Ω) (U : ℕ → Ξ → ℝ)
    -- USER-INPUT (hU_dom, hU_conv): uniform convergence of the empirical criterion,
    -- phrased through a measurable envelope U (input to the internal consistency
    -- step); vdV Thm 5.7 route
    (hU_dom : ∀ n ξ θ,
      |empiricalAvg (stabilizedLogCriterion M θ₀ θ) n
          (fun i : Fin n => X i.val ξ) -
        stabilizedPopulationCriterion M μ θ₀ θ| ≤ U n ξ)
    -- (second half of the envelope input above)
    (hU_conv : TendstoInMeasure ν U atTop (fun _ => (0 : ℝ)))
    (ℓ : Ω → EuclideanSpace ℝ (Fin d))
    -- LEAN-ONLY: a measurable representative of the score; no scope change.
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at θ₀ with score ℓ;
    -- vdV Thm 5.39
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (menv : Ω → ℝ)
    -- USER-INPUT (menv, hmenv, ρ, hρ, hLip): local log-likelihood Lipschitz envelope
    -- with P_{θ₀} ṁ² < ∞ on a ball around θ₀; vdV Thm 5.39
    (hmenv : MemLp menv 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- LEAN-ONLY: a measurable representative for the envelope; no scope change.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- (radius of the Lipschitz neighbourhood; part of the envelope input above)
    (hρ : 0 < ρ)
    -- (the Lipschitz condition itself; part of the envelope input above)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ,
      ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ x,
        |M.logDensity θ₁ x - M.logDensity θ₂ x| ≤
          menv x * ‖θ₁ - θ₂‖)
    -- USER-INPUT: nonsingular Fisher information at θ₀ (positive definiteness);
    -- vdV Thm 5.39
    (hI : (fisherInformationMatrix M μ θ₀ ℓ).PosDef)
    -- LEAN-ONLY: measurability of the sample coordinates; no scope change.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT (hX_indep, hX_id, hX_law): X₁, X₂, … iid with the true model law
    -- P_{θ₀}; vdV §5.5
    (hX_indep : ProbabilityTheory.iIndepFun X ν)
    -- (second component of the iid input above)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) ν ν)
    -- (third component of the iid input above)
    (hX_law : ν.map (X 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- LEAN-ONLY: estimator measurability for pushforward laws; no scope change.
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    -- USER-INPUT: θ̂ₙ maximizes the product likelihood (exact MLE); vdV §5.5
    (hMLE : IsMaximumLikelihoodEstimator M θ_hat) :
    TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (fisherInformationMatrix M μ θ₀ ℓ)⁻¹
            (empiricalProcessVec
              (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
              (fun _ i x => ℓ x i) θ₀ n
              (fun i : Fin n => X i.val ξ))) ∧
      WeakConverges
        (fun n => ν.map (fun ξ =>
          Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0
          (fisherInformationMatrix M μ θ₀ ℓ)⁻¹) := by
  letI : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    withDensity_density_isProbabilityMeasure M μ hPDF θ₀
  have hConsistent : TendstoInProbZero (fun _ : ℕ => ν)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) :=
    mle_consistentInProb_of_kl_identifiable M μ θ₀ hPDF hident husc hcompact
      θ_hat ν X U hU_dom hU_conv hX_meas hX_id hX_law hMLE
  have hm_meas : ∀ θ, Measurable (M.logDensity θ) := by
    intro θ
    exact (M.density_meas θ).log
  have hmdot_meas : ∀ i : Fin d, Measurable (fun x => ℓ x i) :=
    fun i => (measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 (Fin d → ℝ)).comp hℓ)
  have hψ_L2 : MemLp (psiVec (fun _ i x => ℓ x i) θ₀) 2
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    dqm_scoreVector_memLp_two M μ θ₀ ℓ hℓ hPDF hDQM
  have hPmdot_zero : ∀ i : Fin d,
      ∫ x, ℓ x i ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) = 0 :=
    fun i => dqm_scoreCoordinate_mean_zero M μ θ₀ ℓ hℓ hPDF hDQM i
  have hdiff₀ := dqm_logDensity_differentiableInProbabilityAt M μ θ₀ ℓ hPDF hDQM
  have hdiff : DifferentiableInProbabilityAt
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
      (fun θ => M.logDensity θ)
      (MEstimator.mdotProbabilityDerivative (fun i x => ℓ x i) θ₀) θ₀ := by
    simpa only [MEstimator.mdotProbabilityDerivative, psiVec_score_eq] using hdiff₀
  have hLip₀ : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ x,
      |M.logDensity θ x - M.logDensity θ₀ x| ≤
        ‖menv x‖ * ‖θ - θ₀‖ := by
    intro θ hθ x
    exact (hLip θ hθ θ₀ (Metric.mem_closedBall_self hρ.le) x).trans
      (by simpa only [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (le_abs_self (menv x)) (norm_nonneg (θ - θ₀)))
  have hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ =>
      distL2 (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
        (fun x => Real.sqrt n *
          (M.logDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.logDensity θ₀ x))
        (fun x => ⟪h, psiVec
          (fun _ : EuclideanSpace ℝ (Fin d) => fun i x => ℓ x i) θ₀ x⟫))
      atTop (nhds 0) := by
    intro h
    exact MEstimator.distL2_localScale_mdot_of_differentiableInProbabilityAt
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
      (fun θ => M.logDensity θ) (fun i x => ℓ x i) θ₀ hdiff
      (fun θ => (hm_meas θ).aestronglyMeasurable) menv hmenv ρ hρ hLip₀ h
  have hFisher : ∀ u : EuclideanSpace ℝ (Fin d),
      Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ := by
    intro u
    exact dqm_fisher_integrable M μ θ₀ ℓ (hPDF.density_integrable θ₀) hDQM u
      (fun t => hPDF.density_integrable (θ₀ + t • u))
  have hTaylor₀ := dqm_logDensity_populationTaylor M μ θ₀ ℓ hPDF hDQM
    menv hmenv ρ hρ hLip₀
  have hTaylor : Asymptotics.IsLittleO (nhds θ₀)
      (fun θ => (∫ x, (M.logDensity θ x - M.logDensity θ₀ x)
          ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))) -
        (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
          (-(fisherInformationMatrix M μ θ₀ ℓ)) (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2) := by
    convert hTaylor₀ using 1
    funext θ
    rw [fisherInformation_eq_inner_fisherInformationMatrix M μ θ₀ ℓ hFisher]
    simp only [map_neg, ContinuousLinearMap.neg_apply, inner_neg_right]
    ring
  obtain ⟨c, hc, hVsymm, _, hVneg⟩ :=
    neg_posDef_as_mEstimator_curvature (I := fisherInformationMatrix M μ θ₀ ℓ) hI
  have hFixedComparison : ∀ a : EuclideanSpace ℝ (Fin d),
      TendstoInProbZero (fun _ : ℕ => ν) (fun n ξ =>
        (n : ℝ) * max 0
          (empiricalAvg
              (M.logDensity (θ₀ + (Real.sqrt n)⁻¹ • a)) n
              (fun i : Fin n => X i.val ξ) -
            empiricalAvg
              (M.logDensity (θ_hat n (fun i : Fin n => X i.val ξ))) n
              (fun i : Fin n => X i.val ξ))) := by
    intro a
    exact mle_logDensity_fixedComparison_tendstoInProbZero M μ θ₀ ℓ hPDF hDQM
      θ_hat ν X hX_meas hX_id hX_law hMLE a
  have hT8 := MEstimator.m_estimator_normality_of_distL2_fixed_comparisons
    (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    (fun θ => M.logDensity θ) (fun i x => ℓ x i) θ₀
    (-(fisherInformationMatrix M μ θ₀ ℓ)) hVsymm hc hVneg hm_meas
    hmdot_meas hψ_L2 hPmdot_zero menv hmenv hmenv_meas ρ hρ hLip hd hTaylor
    θ_hat ν X hX_meas hX_indep hX_id hX_law hθhat_meas hFixedComparison hConsistent
  have hIdet : IsUnit (fisherInformationMatrix M μ θ₀ ℓ).det :=
    (Matrix.isUnit_iff_isUnit_det (fisherInformationMatrix M μ θ₀ ℓ)).mp hI.isUnit
  have hInvNeg : (-(fisherInformationMatrix M μ θ₀ ℓ))⁻¹ =
      -(fisherInformationMatrix M μ θ₀ ℓ)⁻¹ := by
    simpa using
      Matrix.inv_smul' (fisherInformationMatrix M μ θ₀ ℓ) (-1 : ℝˣ) hIdet
  refine ⟨?_, ?_⟩
  · simpa only [hInvNeg, map_neg, ContinuousLinearMap.neg_apply, sub_eq_add_neg] using hT8.1
  · rw [psiCov_score_eq_fisherInformationMatrix M μ θ₀ ℓ,
      mEstimator_fisher_covariance_collapse
        (fisherInformationMatrix M μ θ₀ ℓ) hI] at hT8
    exact hT8.2

end AsymptoticStatistics.MaximumLikelihood
