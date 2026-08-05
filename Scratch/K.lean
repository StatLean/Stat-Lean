import StatLean.TimeSeries.Mixing.KernelRegressionCLT

set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- local copies of the private ledger defs
noncomputable def bigBlockLen' (h : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) * h n) / Real.log n⌉₊

noncomputable def smallBlockLen' (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : ℕ :=
  ⌈(Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1))⌉₊

noncomputable def blockCount' (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : ℕ :=
  n / (bigBlockLen' h n + smallBlockLen' h δ lam n)

/-! ### Step A: the weighted tail decays one power faster -/

theorem stepA {a : ℕ → ℝ} {lam beta : ℝ} (hlam : 0 < lam) (hbeta : 0 < beta)
    (ha0 : ∀ t, 0 ≤ a t) (hanti : Antitone a)
    (hsum : Summable fun t : ℕ => (t : ℝ) ^ lam * a t ^ beta) :
    Tendsto (fun t : ℕ => (t : ℝ) ^ (lam + 1) * a t ^ beta) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun t => (t : ℝ) ^ lam * a t ^ beta with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg (ha0 t) _)
  have hS : Tendsto (fun k => ∑ j ∈ Finset.range k, f j) atTop (𝓝 (∑' j, f j)) :=
    hsum.hasSum.tendsto_sum_nat
  have hdiv : Tendsto (fun T : ℕ => T / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩
  have hg : Tendsto (fun T : ℕ =>
      (∑ j ∈ Finset.range T, f j) - ∑ j ∈ Finset.range (T / 2), f j) atTop (𝓝 0) := by
    have := hS.sub (hS.comp hdiv)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun t =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg (ha0 t) _)) ?_
    (by simpa using hg.const_mul ((4 : ℝ) ^ (lam + 1)))
  filter_upwards [eventually_ge_atTop 2] with T hT
  set m : ℕ := T / 2 with hm
  have hmT : m ≤ T := Nat.div_le_self _ _
  have hm1 : 1 ≤ m := Nat.one_le_div_iff (by norm_num) |>.2 hT
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  -- each term of the block dominates `m ^ lam * a T ^ beta`
  have hterm : ∀ j ∈ Finset.Ico m T, (m : ℝ) ^ lam * a T ^ beta ≤ f j := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have h1 : (m : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
      Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hj.1) hlam.le
    have h2 : a T ^ beta ≤ a j ^ beta :=
      Real.rpow_le_rpow (ha0 T) (hanti hj.2.le) hbeta.le
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (ha0 T) _)
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hcard : m ≤ (Finset.Ico m T).card := by
    rw [Nat.card_Ico]
    omega
  have hblock : (m : ℝ) ^ (lam + 1) * a T ^ beta
      ≤ ∑ j ∈ Finset.Ico m T, f j := by
    have hcast : (m : ℝ) ≤ ((Finset.Ico m T).card : ℝ) := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ (m : ℝ) ^ lam * a T ^ beta :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (Real.rpow_nonneg (ha0 T) _)
    calc (m : ℝ) ^ (lam + 1) * a T ^ beta
        = (m : ℝ) * ((m : ℝ) ^ lam * a T ^ beta) := by
          rw [Real.rpow_add hmpos, Real.rpow_one, mul_comm ((m:ℝ)^lam), mul_assoc]
      _ ≤ ((Finset.Ico m T).card : ℝ) * ((m : ℝ) ^ lam * a T ^ beta) :=
          mul_le_mul_of_nonneg_right hcast hnn
      _ = (Finset.Ico m T).card • ((m : ℝ) ^ lam * a T ^ beta) := (nsmul_eq_mul _ _).symm
      _ ≤ ∑ j ∈ Finset.Ico m T, f j := Finset.card_nsmul_le_sum _ _ _ hterm
  -- and `T ≤ 4 m`
  have hT4 : (T : ℝ) ≤ 4 * (m : ℝ) := by
    have : T ≤ 4 * m := by omega
    exact_mod_cast this
  have hTle : (T : ℝ) ^ (lam + 1) ≤ (4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1) := by
    calc (T : ℝ) ^ (lam + 1) ≤ (4 * (m : ℝ)) ^ (lam + 1) :=
          Real.rpow_le_rpow (Nat.cast_nonneg T) hT4 (by linarith)
      _ = (4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)
  calc (T : ℝ) ^ (lam + 1) * a T ^ beta
      ≤ ((4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1)) * a T ^ beta :=
        mul_le_mul_of_nonneg_right hTle (Real.rpow_nonneg (ha0 T) _)
    _ = (4 : ℝ) ^ (lam + 1) * ((m : ℝ) ^ (lam + 1) * a T ^ beta) := by ring
    _ ≤ (4 : ℝ) ^ (lam + 1) * ∑ j ∈ Finset.Ico m T, f j :=
        mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (by norm_num) _)
    _ = (4 : ℝ) ^ (lam + 1) *
          ((∑ j ∈ Finset.range T, f j) - ∑ j ∈ Finset.range m, f j) := by
        rw [Finset.sum_Ico_eq_sub _ hmT]

/-! ### Step B -/

theorem stepB [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ =>
        (blockCount' h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen' h δ lam n))
      atTop (𝓝 0) := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by
    rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hlam1 : (0 : ℝ) < lam + 1 := by linarith
  -- `A n = √(n/h n) · log n`, the upper bound for the block count `k_n`
  have hA : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / h n) * Real.log n) atTop atTop := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hq : Tendsto (fun n : ℕ => (n : ℝ) / h n) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
      filter_upwards [hh.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn
      calc (n : ℝ) = (n : ℝ) / 1 := by ring
        _ ≤ (n : ℝ) / h n := div_le_div_of_nonneg_left (Nat.cast_nonneg n) (hh0 n) hn
    exact (Real.tendsto_sqrt_atTop.comp hq).atTop_mul_atTop₀ hlog
  -- the small block length tends to infinity
  have hs_top : Tendsto (fun n : ℕ => smallBlockLen' h δ lam n) atTop atTop := by
    refine tendsto_nat_ceil_atTop.comp ?_
    exact (tendsto_rpow_atTop (div_pos hβ0 hlam1)).comp hA
  -- `k_n ≤ A n`
  have hk_le : ∀ᶠ n : ℕ in atTop, (blockCount' h δ lam n : ℝ)
      ≤ Real.sqrt ((n : ℝ) / h n) * Real.log n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    have hbig : 0 < Real.sqrt ((n : ℝ) * h n) / Real.log n :=
      div_pos (Real.sqrt_pos.2 (mul_pos hnpos (hh0 n))) hlogpos
    have hl : Real.sqrt ((n : ℝ) * h n) / Real.log n ≤ (bigBlockLen' h n : ℝ) :=
      Nat.le_ceil _
    have hlpos : (0 : ℝ) < (bigBlockLen' h n : ℝ) := lt_of_lt_of_le hbig hl
    have hkey : (n : ℝ) / (Real.sqrt ((n : ℝ) * h n) / Real.log n)
        = Real.sqrt ((n : ℝ) / h n) * Real.log n := by
      have h1 : Real.sqrt ((n : ℝ) * h n) = Real.sqrt n * Real.sqrt (h n) :=
        Real.sqrt_mul hnpos.le _
      have h2 : Real.sqrt ((n : ℝ) / h n) = Real.sqrt n / Real.sqrt (h n) :=
        Real.sqrt_div hnpos.le _
      have h3 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt hnpos.le
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnpos
      have hsh : (0 : ℝ) < Real.sqrt (h n) := Real.sqrt_pos.2 (hh0 n)
      rw [h1, h2]
      field_simp
      nlinarith [h3, hsn, hsh, hlogpos]
    calc (blockCount' h δ lam n : ℝ)
        ≤ (n : ℝ) / ((bigBlockLen' h n + smallBlockLen' h δ lam n : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ ≤ (n : ℝ) / (bigBlockLen' h n : ℝ) := by
          rw [Nat.cast_add]
          exact div_le_div_of_nonneg_left hnpos.le hlpos
            (le_add_of_nonneg_right (Nat.cast_nonneg _))
      _ ≤ (n : ℝ) / (Real.sqrt ((n : ℝ) * h n) / Real.log n) :=
          div_le_div_of_nonneg_left hnpos.le hbig hl
      _ = Real.sqrt ((n : ℝ) / h n) * Real.log n := hkey
  -- the main pointwise bound
  have hmain : ∀ᶠ n : ℕ in atTop,
      (blockCount' h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen' h δ lam n)
        ≤ (((smallBlockLen' h δ lam n : ℝ)) ^ (lam + 1) *
            pairAlphaCoeff X e μ (smallBlockLen' h δ lam n) ^ (1 - 2 / δ)) ^ (1 / (1 - 2 / δ)) := by
    filter_upwards [hk_le, hA.eventually_gt_atTop 0] with n hk hA0
    have ha0 : 0 ≤ pairAlphaCoeff X e μ (smallBlockLen' h δ lam n) :=
      pairAlphaCoeff_nonneg X e _
    have hspos : (0 : ℝ) ≤ (smallBlockLen' h δ lam n : ℝ) := Nat.cast_nonneg _
    -- `A n ≤ s_n ^ ((lam+1)/β)`
    have hsge : (Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1))
        ≤ (smallBlockLen' h δ lam n : ℝ) := Nat.le_ceil _
    have hs1 : Real.sqrt ((n : ℝ) / h n) * Real.log n
        ≤ (smallBlockLen' h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) := by
      have hd2 : δ - 2 ≠ 0 := (by linarith : (0:ℝ) < δ - 2).ne'
      have hpq : ((1 - 2 / δ) / (lam + 1)) * ((lam + 1) / (1 - 2 / δ)) = 1 := by
        field_simp [hd2, hlam1.ne']
      have hid : ((Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1)))
            ^ ((lam + 1) / (1 - 2 / δ)) = Real.sqrt ((n : ℝ) / h n) * Real.log n := by
        rw [← Real.rpow_mul hA0.le, hpq, Real.rpow_one]
      calc Real.sqrt ((n : ℝ) / h n) * Real.log n
          = ((Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1)))
              ^ ((lam + 1) / (1 - 2 / δ)) := hid.symm
        _ ≤ (smallBlockLen' h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hsge (div_pos hlam1 hβ0).le
    -- the right-hand side splits
    have hrhs : (((smallBlockLen' h δ lam n : ℝ)) ^ (lam + 1) *
          pairAlphaCoeff X e μ (smallBlockLen' h δ lam n) ^ (1 - 2 / δ)) ^ (1 / (1 - 2 / δ))
        = (smallBlockLen' h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) *
            pairAlphaCoeff X e μ (smallBlockLen' h δ lam n) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hspos _) (Real.rpow_nonneg ha0 _),
        ← Real.rpow_mul hspos, ← Real.rpow_mul ha0, mul_one_div, mul_one_div,
        div_self hβ0.ne', Real.rpow_one]
    rw [hrhs]
    exact mul_le_mul (hk.trans hs1) le_rfl ha0 (Real.rpow_nonneg hspos _)
  refine squeeze_zero' ?_ hmain ?_
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (pairAlphaCoeff_nonneg X e _)
  · have hcomp := (stepA (a := pairAlphaCoeff X e μ) hlam0 hβ0
      (fun t => pairAlphaCoeff_nonneg X e t) (pairAlphaCoeff_antitone X e) hα).comp hs_top
    have hcont : Tendsto (fun y : ℝ => y ^ (1 / (1 - 2 / δ))) (𝓝 0) (𝓝 0) := by
      have hpos : (0 : ℝ) < 1 / (1 - 2 / δ) := one_div_pos.2 hβ0
      have hz : (0 : ℝ) ^ (1 / (1 - 2 / δ)) = 0 := Real.zero_rpow hpos.ne'
      have ht := (Real.continuousAt_rpow_const (0 : ℝ) (1 / (1 - 2 / δ))
        (Or.inr hpos.le)).tendsto
      rw [hz] at ht
      exact ht
    exact hcont.comp hcomp

end StatLean.TimeSeries
