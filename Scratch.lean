import StatLean.RobustStatistics.MEstimation.Influence

open MeasureTheory Filter Topology
open scoped NNReal

namespace StatLean.RobustStatistics

theorem t_mLocationRoot_influence {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ ψ' : ℝ → ℝ} {C : ℝ} {θ : ℝ → ℝ} {θ₀ x₀ d A : ℝ}
    (hψ : ∀ u, HasDerivAt ψ (ψ' u) u)
    (hψ'b : ∀ u, |ψ' u| ≤ C)
    (hint : Integrable (fun x => ψ (x - θ₀)) P)
    (hψ'_meas : Measurable ψ')
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hA : A = ∫ x, ψ' (x - θ₀) ∂P)
    (hA0 : A ≠ 0) :
    d = ψ (x₀ - θ₀) / A := by
  have hdiff : Differentiable ℝ ψ := fun u => (hψ u).differentiableAt
  have hlip : LipschitzWith (Real.toNNReal C) ψ := by
    refine lipschitzWith_of_nnnorm_deriv_le hdiff fun u => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', (hψ u).deriv, Real.norm_eq_abs]
    exact le_max_of_le_left (hψ'b u)
  exact mLocationRoot_influence_of_lipschitz (ψd := fun x => ψ' (x - θ₀)) hlip hint
    (Filter.Eventually.of_forall fun x => hψ (x - θ₀))
    (hψ'_meas.comp (measurable_id.sub_const θ₀)).aestronglyMeasurable hroot hθ0 hθd hA hA0

theorem t_mLocationFunctional_hasInfluenceAt {P : Measure ℝ} [IsProbabilityMeasure P]
    {T : Measure ℝ → ℝ} {ψ ψd : ℝ → ℝ} {L : ℝ≥0} {x₀ A : ℝ}
    (hψlip : LipschitzWith L ψ)
    (hint : Integrable (fun x => ψ (x - T P)) P)
    (hae : ∀ᵐ x ∂P, HasDerivAt ψ (ψd x) (x - T P))
    (hψd_meas : AEStronglyMeasurable ψd P)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t)
        (T (contaminate P (Measure.dirac x₀) t)))
    (hTd : ∃ d, HasDerivWithinAt (fun t : ℝ => T (contaminate P (Measure.dirac x₀) t)) d
      (Set.Ici 0) 0)
    (hA : A = ∫ x, ψd x ∂P) (hA0 : A ≠ 0) :
    HasInfluenceAt T P x₀ (ψ (x₀ - T P) / A) := by
  obtain ⟨d, hd⟩ := hTd
  have hθ0 : (fun t : ℝ => T (contaminate P (Measure.dirac x₀) t)) 0 = T P := by
    simp
  have hval := mLocationRoot_influence_of_lipschitz
    (θ := fun t : ℝ => T (contaminate P (Measure.dirac x₀) t)) (θ₀ := T P)
    hψlip hint hae hψd_meas hroot hθ0 hd hA hA0
  rw [hasInfluenceAt_iff_hasDerivWithinAt, ← hval]
  exact hd

theorem t_mLocation_influence_bounded {ψ : ℝ → ℝ} {c A u : ℝ}
    (hψb : ∀ v, |ψ v| ≤ c) (hA0 : A ≠ 0) :
    |ψ u / A| ≤ c / |A| := by
  rw [abs_div]
  exact div_le_div_of_nonneg_right (hψb u) (abs_nonneg A)

/-! ### Huber -/

example {c : ℝ} (hc : 0 < c) {θ₀ u : ℝ} (hne₁ : u ≠ c) (hne₂ : u ≠ -c) :
    HasDerivAt (huberPsi c) (if |u| < c then (1 : ℝ) else 0) u := by
  by_cases h : |u| < c
  · rw [if_pos h]
    have hopen : IsOpen {v : ℝ | |v| < c} := isOpen_lt continuous_abs continuous_const
    refine (hasDerivAt_id u).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h] with v hv
    exact huberPsi_of_abs_le hc.le (le_of_lt hv)
  · rw [if_neg h]
    rcases lt_or_gt_of_ne hne₁ with h1 | h1
    · -- u < c ; and ¬|u| < c so u ≤ -c, with u ≠ -c gives u < -c
      have hu : u < -c := by
        rcases lt_or_gt_of_ne hne₂ with h2 | h2
        · exact h2
        · exact absurd (abs_lt.mpr ⟨h2, h1⟩) h
      have hopen : IsOpen {v : ℝ | v < -c} := isOpen_lt continuous_id continuous_const
      refine (hasDerivAt_const u (-c)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hu] with v hv
      have hv' : v ≤ c := le_trans hv.le (by linarith)
      simp [huberPsi, min_eq_right hv', max_eq_left hv.le]
    · have hopen : IsOpen {v : ℝ | c < v} := isOpen_lt continuous_const continuous_id
      refine (hasDerivAt_const u c).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds h1] with v hv
      simp [huberPsi, min_eq_left hv.le, max_eq_right (by linarith : -c ≤ c)]

end StatLean.RobustStatistics
