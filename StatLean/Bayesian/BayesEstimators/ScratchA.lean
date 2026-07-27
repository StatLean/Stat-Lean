import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! SCRATCH FILE (temporary, not imported anywhere). Two pure real-analysis bricks. -/

open Filter Topology

namespace ScratchA

private lemma continuous_rpow_const_of_nonneg {p : ℝ} (hp : 0 ≤ p) :
    Continuous fun t : ℝ => t ^ p :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr hp)

private lemma tendsto_exp_neg_half_mul :
    Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (-(1 / 2) : ℝ) * x) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0)).2 tendsto_id
  exact Real.tendsto_exp_atBot.comp h

/-- A polynomial times a Gaussian is bounded on `[0, ∞)`. -/
theorem exists_poly_exp_bound {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t ^ p) * Real.exp (-c * t ^ 2) ≤ K := by
  have hcont : Continuous fun t : ℝ => (1 + t ^ p) * Real.exp (-c * t ^ 2) :=
    (continuous_const.add (continuous_rpow_const_of_nonneg hp)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2)))
  have h1 : Tendsto (fun t : ℝ => Real.exp (-c * t ^ 2)) atTop (𝓝 0) :=
    (exp_neg_mul_sq_isLittleO_exp_neg hc).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun t : ℝ => t ^ p * Real.exp (-c * t ^ 2)) atTop (𝓝 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hc p).trans_tendsto tendsto_exp_neg_half_mul
  have hlim : Tendsto (fun t : ℝ => (1 + t ^ p) * Real.exp (-c * t ^ 2)) atTop (𝓝 0) := by
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3.congr fun t => by ring
  obtain ⟨T, hT⟩ :=
    eventually_atTop.1 (hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  have hcpt : IsCompact (Set.Icc (0 : ℝ) (max T 0)) := isCompact_Icc
  obtain ⟨t₀, -, ht₀⟩ := hcpt.exists_isMaxOn ⟨0, by simp⟩ hcont.continuousOn
  refine ⟨max 1 ((1 + t₀ ^ p) * Real.exp (-c * t₀ ^ 2)),
    lt_of_lt_of_le one_pos (le_max_left _ _), fun t ht => ?_⟩
  rcases le_or_gt t (max T 0) with h | h
  · exact le_trans (ht₀ (Set.mem_Icc.2 ⟨ht, h⟩)) (le_max_right _ _)
  · exact le_trans (hT t ((le_max_left T 0).trans h.le)) (le_max_left _ _)

/-- **The pointwise weight-absorption inequality**. -/
theorem weighted_exp_split {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * n * min (r ^ 2) 1)
        ≤ K * Real.exp (-(c / 2) * n * min (r ^ 2) 1)
          + K * (1 + r ^ p) * Real.exp (-(c / 2) * n) := by
  obtain ⟨K, hK, hKb⟩ := exists_poly_exp_bound hp (half_pos hc)
  refine ⟨K, hK, fun n r hr => ?_⟩
  have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hrp : (0 : ℝ) ≤ r ^ p := Real.rpow_nonneg hr p
  rcases le_or_gt r 1 with hr1 | hr1
  · have hmin : min (r ^ 2) 1 = r ^ 2 := min_eq_left (by nlinarith)
    simp only [hmin]
    have h1 := hKb (Real.sqrt n * r) (mul_nonneg hs hr)
    rw [show (Real.sqrt n * r) ^ 2 = (n : ℝ) * r ^ 2 by rw [mul_pow, hsq]] at h1
    have key : (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * (n : ℝ) * r ^ 2)
        ≤ K * Real.exp (-(c / 2) * (n : ℝ) * r ^ 2) := by
      have e : Real.exp (-c * (n : ℝ) * r ^ 2)
          = Real.exp (-(c / 2) * ((n : ℝ) * r ^ 2)) * Real.exp (-(c / 2) * (n : ℝ) * r ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    refine key.trans (le_add_of_nonneg_right ?_)
    exact mul_nonneg (mul_nonneg hK.le (by linarith)) (Real.exp_pos _).le
  · have hmin : min (r ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    simp only [hmin, mul_one]
    set E := Real.exp (-(c / 2) * (n : ℝ)) with hEdef
    have hEpos : 0 < E := Real.exp_pos _
    set S := Real.sqrt n ^ p with hSdef
    have hSnn : 0 ≤ S := Real.rpow_nonneg hs p
    have h1 : (1 + S) * E ≤ K := by
      have h := hKb (Real.sqrt n) hs
      rw [hsq] at h
      exact h
    have hEK : E ≤ K := by nlinarith
    have hSEK : S * E ≤ K := by nlinarith
    have hmain : (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * (n : ℝ))
        ≤ K * (1 + r ^ p) * E := by
      have hmr : (Real.sqrt n * r) ^ p = S * r ^ p := Real.mul_rpow hs hr
      have he : Real.exp (-c * (n : ℝ)) = E * E := by
        rw [hEdef, ← Real.exp_add]; congr 1; ring
      rw [hmr, he, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hEpos.le
      nlinarith [mul_nonneg (sub_nonneg.2 hSEK) hrp]
    have : (0 : ℝ) ≤ K * E := mul_nonneg hK.le hEpos.le
    linarith

/-- Auxiliary: `n^{k/2} e^{-a n} → 0`. -/
theorem sqrt_pow_mul_exp_neg_tendsto (kk : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.sqrt n ^ kk * Real.exp (-a * n)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hKb⟩ :=
    exists_poly_exp_bound (p := (kk : ℝ)) (Nat.cast_nonneg kk) (half_pos ha)
  have key : ∀ n : ℕ, Real.sqrt n ^ kk * Real.exp (-a * (n : ℝ))
      ≤ K * Real.exp (-(a / 2) * (n : ℝ)) := by
    intro n
    have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have h1 := hKb (Real.sqrt n) hs
    rw [hsq] at h1
    have hnat : Real.sqrt n ^ kk = Real.sqrt n ^ (kk : ℝ) := (Real.rpow_natCast _ kk).symm
    have hnn : (0 : ℝ) ≤ Real.sqrt n ^ (kk : ℝ) := Real.rpow_nonneg hs _
    have hEpos : (0 : ℝ) < Real.exp (-(a / 2) * (n : ℝ)) := Real.exp_pos _
    have h3 : Real.sqrt n ^ kk * Real.exp (-(a / 2) * (n : ℝ)) ≤ K := by
      rw [hnat]
      nlinarith
    have he : Real.exp (-a * (n : ℝ))
        = Real.exp (-(a / 2) * (n : ℝ)) * Real.exp (-(a / 2) * (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h3 hEpos.le
  have hg : Tendsto (fun n : ℕ => K * Real.exp (-(a / 2) * (n : ℝ))) atTop (𝓝 0) := by
    have hb : Real.exp (-(a / 2)) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.2 (by linarith)
    have h0 : (0 : ℝ) ≤ Real.exp (-(a / 2)) := (Real.exp_pos _).le
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hb).const_mul K
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [mul_comm (-(a / 2) : ℝ) (n : ℝ), Real.exp_nat_mul]
  refine squeeze_zero (fun n => ?_) key hg
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_pos _).le

end ScratchA
