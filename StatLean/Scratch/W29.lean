import StatLean.HypothesisTesting.ForMathlib.MultivariateBerryEsseen

/-! Scratch module for wave-29 BENT.  DELETE before committing. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators InnerProductSpace Real

namespace StatLean.HypothesisTesting

namespace W29

variable {k : ℕ}

lemma map_partial_sum_eq_smul_sumLaw {n j : ℕ} (hj : j ≤ n) (hm : 0 < n - j)
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] :
    ((Measure.pi fun i : Fin n =>
        if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
      = (sumLaw (n - j) ν).map
          (fun x => (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x) := sorry

set_option maxHeartbeats 1600000 in
/-- Generic conditioning skeleton. -/
lemma hybridLaw_le_of_affine_le {n j : ℕ} (hn : 0 < n) (hj : j ≤ n)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    {S : Set (EuclideanSpace ℝ (Fin k))} (hSm : MeasurableSet S) {c : ℝ} (hc : 0 ≤ c)
    (hG : n ≤ 2 * j → ∀ r : ℝ, 1 / 2 ≤ r → ∀ a : EuclideanSpace ℝ (Fin k),
      ((stdGaussian (EuclideanSpace ℝ (Fin k))) ((fun x => r • x + a) ⁻¹' S)).toReal ≤ c)
    (hM : 2 * j < n → ∀ r : ℝ, 1 / 2 ≤ r → ∀ a : EuclideanSpace ℝ (Fin k),
      ((sumLaw (n - j) ν) ((fun x => r • x + a) ⁻¹' S)).toReal ≤ c) :
    ((hybridLaw n j ν) S).toReal ≤ c := by
  haveI hinst : ∀ i : Fin n, IsProbabilityMeasure
      (if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) := by
    intro i; split <;> infer_instance
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  suffices h : hybridLaw n j ν S ≤ ENNReal.ofReal c by
    calc (hybridLaw n j ν S).toReal
        ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono (by simp) h
      _ = c := ENNReal.toReal_ofReal hc
  have hΦ : Measurable (fun p : (Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k) =>
      (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
        + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) := by fun_prop
  rw [hybridLaw, Measure.map_apply hΦ hSm]
  rcases le_or_gt n (2 * j) with hcase | hcase
  · have hjpos : 0 < j := by omega
    have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
    have hσpos : (0 : ℝ) < Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ) := by positivity
    have hσsq : (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) ^ 2 = (j : ℝ) / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hjr.le, Real.sq_sqrt hnr.le]
    have hσge : (1 : ℝ) / 2 ≤ Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ) := by
      have hhalf : (1 : ℝ) / 2 ≤ (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) ^ 2 := by
        rw [hσsq, le_div_iff₀ hnr]
        have : (n : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hcase
        linarith
      nlinarith
    rw [Measure.prod_apply (hΦ hSm)]
    have hinner : ∀ y : Fin n → EuclideanSpace ℝ (Fin k),
        (stdGaussian (EuclideanSpace ℝ (Fin k)))
            (Prod.mk y ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
                × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
                  + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          ≤ ENNReal.ofReal c := by
      intro y
      have hset : (Prod.mk y ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
            × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
              + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          = (fun z => (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • z
              + (Real.sqrt (n : ℝ))⁻¹ • (∑ i, y i)) ⁻¹' S := by
        ext z
        simp only [Set.mem_preimage]
        rw [add_comm]
      rw [hset]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).2
        (hG hcase _ hσge ((Real.sqrt (n : ℝ))⁻¹ • (∑ i, y i)))
    calc ∫⁻ y, (stdGaussian (EuclideanSpace ℝ (Fin k))) (Prod.mk y ⁻¹' _)
            ∂(Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
        ≤ ∫⁻ _, ENNReal.ofReal c
            ∂(Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν) :=
          lintegral_mono hinner
      _ = ENNReal.ofReal c := by rw [lintegral_const, measure_univ, mul_one]
  · have hm : 0 < n - j := by omega
    have hmn : n ≤ 2 * (n - j) := by omega
    have hmr : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast hm
    have hlampos : (0 : ℝ) < Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by positivity
    have hlamsq : (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) ^ 2
        = ((n - j : ℕ) : ℝ) / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hmr.le, Real.sq_sqrt hnr.le]
    have hlamge : (1 : ℝ) / 2 ≤ Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by
      have hhalf : (1 : ℝ) / 2 ≤ (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) ^ 2 := by
        rw [hlamsq, le_div_iff₀ hnr]
        have : (n : ℝ) ≤ 2 * ((n - j : ℕ) : ℝ) := by exact_mod_cast hmn
        linarith
      nlinarith
    rw [Measure.prod_apply_symm (hΦ hSm)]
    have hinner : ∀ z : EuclideanSpace ℝ (Fin k),
        (Measure.pi fun i : Fin n =>
            if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
            ((fun y => (y, z)) ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
                × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
                  + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          ≤ ENNReal.ofReal c := by
      intro z
      set a : EuclideanSpace ℝ (Fin k) := (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • z with hadef
      have hTm : MeasurableSet ((fun w => w + a) ⁻¹' S) := (measurable_id.add_const a) hSm
      have hset : ((fun y : Fin n → EuclideanSpace ℝ (Fin k) => (y, z))
            ⁻¹' ((fun p : (Fin n → EuclideanSpace ℝ (Fin k))
              × EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • (∑ i, p.1 i)
                + (Real.sqrt (j : ℝ) / Real.sqrt (n : ℝ)) • p.2) ⁻¹' S))
          = (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) ⁻¹' ((fun w => w + a) ⁻¹' S) := by
        ext y
        simp only [Set.mem_preimage, hadef]
      rw [hset, ← Measure.map_apply (by fun_prop) hTm,
        map_partial_sum_eq_smul_sumLaw hj hm ν,
        Measure.map_apply (by fun_prop) hTm]
      have hset2 : ((fun x : EuclideanSpace ℝ (Fin k) =>
            (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x)
            ⁻¹' ((fun w => w + a) ⁻¹' S))
          = (fun x => (Real.sqrt ((n - j : ℕ) : ℝ) / Real.sqrt (n : ℝ)) • x + a) ⁻¹' S := rfl
      rw [hset2]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).2
        (hM hcase _ hlamge a)
    calc ∫⁻ z, (Measure.pi fun i : Fin n =>
              if (i : ℕ) < j then Measure.dirac (0 : EuclideanSpace ℝ (Fin k)) else ν)
            ((fun y => (y, z)) ⁻¹' _) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
        ≤ ∫⁻ _, ENNReal.ofReal c ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
          lintegral_mono hinner
      _ = ENNReal.ofReal c := by rw [lintegral_const, measure_univ, mul_one]

/-- Brick H, re-derived. -/
theorem hybridLaw_shell_le' (hk : 0 < k) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    {B : Set (EuclideanSpace ℝ (Fin k))} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {ε : ℝ} (hε : 0 < ε) {Y : ℝ}
    (hY : ∀ m : ℕ, n ≤ 2 * m → m ≤ n →
      convexDiscrepancy (sumLaw m ν) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
        ≤ Y) :
    ((hybridLaw n j ν) (Metric.thickening ε B \ interior B)).toReal
      ≤ 2 * gaussianShellConst k * ε + 2 * Y := by
  have hCk : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  have hY0 : (0 : ℝ) ≤ Y := le_trans convexDiscrepancy_nonneg (hY n (by omega) le_rfl)
  have hgauss : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := multivariateGaussian_zero_one
  have hbound : ∀ r : ℝ, 1 / 2 ≤ r → ε / r ≤ 2 * ε := by
    intro r hr
    have hrpos : (0 : ℝ) < r := by linarith
    rw [div_le_iff₀ hrpos]; nlinarith
  refine hybridLaw_le_of_affine_le hn hj
    (Metric.isOpen_thickening.measurableSet.diff isOpen_interior.measurableSet)
    (by positivity) (fun _ r hr a => ?_) (fun _ r hr a => ?_)
  · have hrpos : (0 : ℝ) < r := by linarith
    have hb := gaussian_measureReal_shell_preimage_aff_le hk hrpos a hBm hBc hε
    rw [← hgauss]
    have := mul_le_mul_of_nonneg_left (hbound r hr) hCk.le
    linarith
  · have hrpos : (0 : ℝ) < r := by linarith
    have hb := measureReal_shell_preimage_aff_le hk (sumLaw (n - j) ν) hrpos a hBm hBc hε
    have hYm := hY (n - j) (by omega) (Nat.sub_le _ _)
    have := mul_le_mul_of_nonneg_left (hbound r hr) hCk.le
    linarith

end W29

end StatLean.HypothesisTesting
