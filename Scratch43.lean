import StatLean.HypothesisTesting.ForMathlib.MultivariateBerryEsseen

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators InnerProductSpace Real

namespace StatLean.HypothesisTesting
namespace Scratch43

variable {k : ℕ}

/-! stubs for the private lemmas of MBE -/

theorem wideShell_le_of_deconvolution {B : Set (EuclideanSpace ℝ (Fin k))}
    {τ η μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ] [IsProbabilityMeasure η]
    (hμ : μ = (τ.prod η).map fun p => p.1 + p.2)
    {Ck W : ℝ} (hCk : 0 ≤ Ck)
    (hshell : ∀ s : ℝ, 0 < s →
      (μ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    {t q : ℝ} (ht : 0 < t) (hq0 : 0 < q)
    (hq : q ≤ (η (Metric.closedBall 0 t)).toReal)
    {s : ℝ} (hs : 0 < s) (hts : t ≤ s) :
    (τ (Metric.thickening s B \ erosion s B)).toReal ≤ (8 * Ck * s + W) / q := sorry

theorem measureReal_closedBall_ge_of_normSq
    {η : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure η]
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) η)
    {t : ℝ} (ht : 0 < t) :
    1 - (∫ y, ‖y‖ ^ 2 ∂η) / t ^ 2
      ≤ (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) t)).toReal := sorry

theorem map_pi_sum_peel' {k m : ℕ}
    (κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (κ i)] (i : Fin (m + 1)) :
    ((Measure.pi κ).map fun x => ∑ l, x l)
      = (((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))).map
          fun p => p.1 + ∑ l, p.2 l) := sorry

/-! ### the real work -/

/-- The two-sided shell is monotone in its width. -/
theorem wideShell_mono {B : Set (EuclideanSpace ℝ (Fin k))} {s t : ℝ} (hst : s ≤ t) :
    Metric.thickening s B \ erosion s B ⊆ Metric.thickening t B \ erosion t B :=
  Set.diff_subset_diff (Metric.thickening_mono hst B)
    (fun _ hx _ hy => hx (Metric.closedBall_subset_closedBall hst hy))

/-- **Deconvolution of a two-sided-shell bound, in uniform form (wave 43).** -/
theorem wideShell_le_of_deconvolution_uniform {B : Set (EuclideanSpace ℝ (Fin k))}
    {τ η μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure τ] [IsProbabilityMeasure η]
    (hμ : μ = (τ.prod η).map fun p => p.1 + p.2)
    {Ck W : ℝ} (hCk : 0 ≤ Ck) (hW : 0 ≤ W)
    (hshell : ∀ s : ℝ, 0 < s →
      (μ (Metric.thickening s B \ erosion s B)).toReal ≤ 4 * Ck * s + W)
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) η)
    {r : ℝ} (hr : 0 < r) (hnorm : (∫ y, ‖y‖ ^ 2 ∂η) ≤ r ^ 2) :
    ∀ s : ℝ, 0 < s → (τ (Metric.thickening s B \ erosion s B)).toReal
      ≤ 4 * (3 * Ck) * s + (2 * W + 22 * Ck * r) := by
  have ht : (0 : ℝ) < 2 * r := by linarith
  have hq : (3 : ℝ) / 4
      ≤ (η (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (2 * r))).toReal := by
    refine le_trans ?_ (measureReal_closedBall_ge_of_normSq h2 ht)
    have hrr : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    rw [hrr]
    have hdiv : (∫ y, ‖y‖ ^ 2 ∂η) / (4 * r ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hbig : ∀ s : ℝ, 2 * r ≤ s → (τ (Metric.thickening s B \ erosion s B)).toReal
      ≤ (32 / 3) * Ck * s + (4 / 3) * W := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht hs
    have h := wideShell_le_of_deconvolution hμ hCk hshell ht (by norm_num) hq hs0 hs
    have hrw : (8 * Ck * s + W) / (3 / 4) = (32 / 3) * Ck * s + (4 / 3) * W := by ring
    rwa [hrw] at h
  intro s hs
  rcases le_total (2 * r) s with hcase | hcase
  · have h := hbig s hcase
    nlinarith [mul_nonneg hCk hs.le, mul_nonneg hCk hr.le]
  · refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (wideShell_mono hcase))) ?_
    refine le_trans (hbig (2 * r) le_rfl) ?_
    nlinarith [mul_nonneg hCk hs.le, mul_nonneg hCk hr.le]

/-! ### the tail radius facts -/

theorem sqrt_dim_le_gaussianTailRadius {k : ℕ} (hk : 0 < k) (σ : ℝ) :
    Real.sqrt (k : ℝ) ≤ gaussianTailRadius k σ := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hmono : Real.log 2 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hbig : (k : ℝ) ≤ 2 * (k : ℝ) * Real.log (2 * (k : ℝ)) := by nlinarith
  have h := Real.sqrt_le_sqrt hbig
  have h2 : 0 ≤ 2 * Real.sqrt ((k : ℝ) * Real.log σ⁻¹) := by positivity
  rw [gaussianTailRadius]
  linarith

theorem gaussianTailRadius_anti {k : ℕ} {ε σ : ℝ} (hε : 0 < ε) (hεσ : ε ≤ σ) :
    gaussianTailRadius k σ ≤ gaussianTailRadius k ε := by
  have hσ : 0 < σ := lt_of_lt_of_le hε hεσ
  have hinv : σ⁻¹ ≤ ε⁻¹ := by rw [inv_le_inv₀ hσ hε]; exact hεσ
  have hlog : Real.log σ⁻¹ ≤ Real.log ε⁻¹ := Real.log_le_log (by positivity) hinv
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h : Real.sqrt ((k : ℝ) * Real.log σ⁻¹) ≤ Real.sqrt ((k : ℝ) * Real.log ε⁻¹) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [gaussianTailRadius, gaussianTailRadius]
  linarith

/-! ### the two convolution identities -/

theorem conv_reassoc {α β ζ : Measure (EuclideanSpace ℝ (Fin k))}
    [SFinite α] [SFinite β] [SFinite ζ] :
    ((α ∗ β) ∗ ζ) = ((β ∗ ζ) ∗ α) := by
  rw [Measure.conv_assoc, Measure.conv_comm α (β ∗ ζ)]

theorem conv_eq_map_add (α β : Measure (EuclideanSpace ℝ (Fin k))) :
    α ∗ β = (α.prod β).map fun p => p.1 + p.2 := rfl

/-- Peeling one coordinate off the *scaled* coordinate-sum law, at the level of measures. -/
theorem map_pi_sum_smul_peel {m : ℕ}
    (κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (κ i)] (i : Fin (m + 1)) (c : ℝ) :
    ((Measure.pi κ).map fun x => c • ∑ l, x l)
      = ((κ i).map fun u => c • u)
        ∗ ((Measure.pi fun l : Fin m => κ (i.succAbove l)).map fun y => c • ∑ l, y l) := by
  have hmeas1 : Measurable fun x : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) =>
      ∑ l, x l := by fun_prop
  have hmeas2 : Measurable fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) => ∑ l, y l := by
    fun_prop
  have hleft : ((Measure.pi κ).map fun x => c • ∑ l, x l)
      = (((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))).map
          fun p => c • p.1 + c • ∑ l, p.2 l) := by
    rw [show (fun x : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) => c • ∑ l, x l)
        = (fun w : EuclideanSpace ℝ (Fin k) => c • w) ∘ (fun x => ∑ l, x l) from rfl,
      ← Measure.map_map (by fun_prop) hmeas1, map_pi_sum_peel' κ i,
      Measure.map_map (by fun_prop) (by fun_prop)]
    have hfun : ((fun w : EuclideanSpace ℝ (Fin k) => c • w)
          ∘ fun p : EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) =>
            p.1 + ∑ l, p.2 l)
        = fun p => c • p.1 + c • ∑ l, p.2 l := by
      funext p
      simp only [Function.comp_apply, smul_add]
    rw [hfun]
  rw [hleft, conv_eq_map_add, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **The head-side convolution identity (wave 43).** -/
theorem hybridLaw_conv_head {m j : ℕ} (hj : j < m + 1)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν]
    {κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k))}
    [∀ i, IsProbabilityMeasure (κ i)]
    (hκ : ∀ i : Fin (m + 1), κ i = if (i : ℕ) < j then Measure.dirac 0 else ν) :
    hybridLaw (m + 1) j ν
      = (((Measure.pi fun l : Fin m => κ ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)).map
            fun y => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • ∑ l, y l)
          ∗ ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
            fun z => (Real.sqrt (j : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) • z))
        ∗ (ν.map fun u => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • u) := by
  have hκeq : κ = fun i : Fin (m + 1) =>
      if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν := funext hκ
  have hν : κ (⟨j, hj⟩ : Fin (m + 1)) = ν := by
    rw [hκ]; exact if_neg (lt_irrefl j)
  rw [hybridLaw_eq_map_add, ← hκeq, ← conv_eq_map_add,
    map_pi_sum_smul_peel κ (⟨j, hj⟩ : Fin (m + 1)) (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹, hν,
    conv_reassoc]

/-- **The tail-side convolution identity (wave 43).** -/
theorem hybridLaw_conv_tail {m j : ℕ} (hj : j < m + 1)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν]
    {κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k))}
    [∀ i, IsProbabilityMeasure (κ i)]
    (hκ : ∀ i : Fin (m + 1), κ i = if (i : ℕ) < j then Measure.dirac 0 else ν) :
    hybridLaw (m + 1) (j + 1) ν
      = ((Measure.pi fun l : Fin m => κ ((⟨j, hj⟩ : Fin (m + 1)).succAbove l)).map
            fun y => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • ∑ l, y l)
        ∗ ((stdGaussian (EuclideanSpace ℝ (Fin k))).map
            fun z => (Real.sqrt ((j + 1 : ℕ) : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) • z) := by
  classical
  set κ' : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun i => if (i : ℕ) < j + 1 then Measure.dirac 0 else ν with hκ'def
  haveI hκ'p : ∀ i, IsProbabilityMeasure (κ' i) := by
    intro i; rw [hκ'def]; dsimp only; split <;> infer_instance
  have hoff : (fun l : Fin m => κ' ((⟨j, hj⟩ : Fin (m + 1)).succAbove l))
      = fun l : Fin m => κ ((⟨j, hj⟩ : Fin (m + 1)).succAbove l) := by
    funext l
    have hne : (((⟨j, hj⟩ : Fin (m + 1)).succAbove l : Fin (m + 1)) : ℕ) ≠ j := by
      intro h
      exact Fin.succAbove_ne (⟨j, hj⟩ : Fin (m + 1)) l (Fin.ext (by rw [h]))
    rw [hκ'def, hκ]
    dsimp only
    by_cases hlt : (((⟨j, hj⟩ : Fin (m + 1)).succAbove l : Fin (m + 1)) : ℕ) < j
    · rw [if_pos (by omega), if_pos hlt]
    · rw [if_neg (by omega), if_neg hlt]
  have hdir : κ' (⟨j, hj⟩ : Fin (m + 1)) = Measure.dirac 0 := by
    rw [hκ'def]; dsimp only; exact if_pos (Nat.lt_succ_self j)
  have hmd : (Measure.dirac (0 : EuclideanSpace ℝ (Fin k))).map
      (fun u => (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • u)
      = Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) := by simp
  rw [hybridLaw_eq_map_add, ← hκ'def, ← conv_eq_map_add,
    map_pi_sum_smul_peel κ' (⟨j, hj⟩ : Fin (m + 1)) (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹, hdir,
    hoff, hmd, Measure.dirac_zero_conv]

end Scratch43
end StatLean.HypothesisTesting
