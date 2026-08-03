import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

namespace A51


lemma nat_pow_mono {n : ℕ} {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (n : ℝ) ^ i ≤ (n : ℝ) ^ j := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    norm_num [zero_pow (show i ≠ 0 by omega), zero_pow (show j ≠ 0 by omega)]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    exact pow_le_pow_right₀ h1 hij

lemma nB2_le8 {n : ℕ} {Bd : ℝ} : (n : ℝ) * Bd ^ 2 ≤ (n : ℝ) ^ 3 + Bd ^ 4 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases le_or_gt ((n : ℝ)) (Bd ^ 2) with h | h
  · nlinarith [pow_nonneg hn 3, sq_nonneg Bd]
  · have h23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := nat_pow_mono (by norm_num) (by norm_num)
    nlinarith [sq_nonneg Bd]

lemma nB_le8 {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) : (n : ℝ) * Bd ≤ (n : ℝ) ^ 3 + Bd ^ 4 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : (n : ℝ) * Bd ≤ (n : ℝ) * Bd ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hn (le_trans zero_le_one hB)) (sub_nonneg.2 hB)]
  exact h.trans nB2_le8

lemma nB4_le10 {n : ℕ} {Bd : ℝ} : (n : ℝ) * Bd ^ 4 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases le_or_gt ((n : ℝ)) (Bd ^ 2) with h | h
  · nlinarith [pow_nonneg hn 4, pow_nonneg (sq_nonneg Bd) 2, sq_nonneg Bd,
      pow_nonneg (sq_nonneg Bd) 3]
  · have h34 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := nat_pow_mono (by norm_num) (by norm_num)
    have hb4 : Bd ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg Bd]
    nlinarith [pow_nonneg (sq_nonneg Bd) 3]

lemma nB3_le10 {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) : (n : ℝ) * Bd ^ 3 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : (n : ℝ) * Bd ^ 3 ≤ (n : ℝ) * Bd ^ 4 := by
    nlinarith [mul_nonneg hn (pow_nonneg (le_trans zero_le_one hB) 3), sub_nonneg.2 hB]
  exact h.trans nB4_le10

lemma nB2_le10 {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) : (n : ℝ) * Bd ^ 2 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : (n : ℝ) * Bd ^ 2 ≤ (n : ℝ) * Bd ^ 3 := by
    nlinarith [mul_nonneg hn (sq_nonneg Bd), sub_nonneg.2 hB]
  exact h.trans (nB3_le10 hB)

lemma Bn3_le10 {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) : Bd * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases le_or_gt Bd ((n : ℝ)) with h | h
  · nlinarith [pow_nonneg hn 3, pow_nonneg (sq_nonneg Bd) 3]
  · have hB0 : (0 : ℝ) ≤ Bd := le_trans zero_le_one hB
    have hb : Bd ^ 4 ≤ Bd ^ 6 := pow_le_pow_right₀ hB (by norm_num)
    have hn3 : (n : ℝ) ^ 3 ≤ Bd ^ 3 := pow_le_pow_left₀ hn h.le 3
    have : Bd * (n : ℝ) ^ 3 ≤ Bd * Bd ^ 3 := by nlinarith
    nlinarith [pow_nonneg hn 4]

lemma Bn2_le10 {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) : Bd * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have h23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := nat_pow_mono (by norm_num) (by norm_num)
  have h : Bd * (n : ℝ) ^ 2 ≤ Bd * (n : ℝ) ^ 3 := by
    nlinarith [le_trans zero_le_one hB]
  exact h.trans (Bn3_le10 hB)

lemma Bn_le10 {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) : Bd * (n : ℝ) ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have h12 : (n : ℝ) ^ 1 ≤ (n : ℝ) ^ 2 := nat_pow_mono (by norm_num) (by norm_num)
  rw [pow_one] at h12
  have h : Bd * (n : ℝ) ≤ Bd * (n : ℝ) ^ 2 := by nlinarith [le_trans zero_le_one hB]
  exact h.trans (Bn2_le10 hB)

lemma B2n2_le10 {n : ℕ} {Bd : ℝ} : Bd ^ 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases le_or_gt ((n : ℝ)) (Bd ^ 2) with h | h
  · have hn2 : (n : ℝ) ^ 2 ≤ (Bd ^ 2) ^ 2 := pow_le_pow_left₀ hn h 2
    have : Bd ^ 2 * (n : ℝ) ^ 2 ≤ Bd ^ 2 * (Bd ^ 2) ^ 2 := by nlinarith [sq_nonneg Bd]
    nlinarith [pow_nonneg hn 4]
  · have h34 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := nat_pow_mono (by norm_num) (by norm_num)
    have : Bd ^ 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
    nlinarith [pow_nonneg (sq_nonneg Bd) 3]

lemma B2n_le10 {n : ℕ} {Bd : ℝ} : Bd ^ 2 * (n : ℝ) ≤ (n : ℝ) ^ 4 + Bd ^ 6 := by
  have h12 : (n : ℝ) ^ 1 ≤ (n : ℝ) ^ 2 := nat_pow_mono (by norm_num) (by norm_num)
  rw [pow_one] at h12
  have h : Bd ^ 2 * (n : ℝ) ≤ Bd ^ 2 * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg Bd]
  exact h.trans B2n2_le10

lemma n_le_n3 {n : ℕ} : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
  have := nat_pow_mono (n := n) (i := 1) (j := 3) (by norm_num) (by norm_num)
  simpa using this

lemma n_le_n4 {n : ℕ} : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
  have := nat_pow_mono (n := n) (i := 1) (j := 4) (by norm_num) (by norm_num)
  simpa using this

lemma n2_le_n3 {n : ℕ} : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 :=
  nat_pow_mono (by norm_num) (by norm_num)

lemma n2_le_n4 {n : ℕ} : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 :=
  nat_pow_mono (by norm_num) (by norm_num)

lemma n3_le_n4 {n : ℕ} : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 :=
  nat_pow_mono (by norm_num) (by norm_num)

/-- The pure `(n, B)` ledger of the order-eight step. -/
lemma step_eight_ledger {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) :
    1120 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) + 84 * ((n : ℝ) ^ 2 + (n : ℝ))
        + 1120 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) + 210 * ((n : ℝ) ^ 2 + (n : ℝ))
        + 56 * ((n : ℝ) * Bd) + 28 * ((n : ℝ) * Bd ^ 2) + Bd ^ 4
      ≤ 2400 * (4 * (n : ℝ) ^ 3 + 6 * (n : ℝ) ^ 2 + 4 * (n : ℝ) + 1 + Bd ^ 4) := by
  have e1 : (n : ℝ) * Bd ^ 2 ≤ (n : ℝ) ^ 3 + Bd ^ 4 := nB2_le8
  have e2 : (n : ℝ) * Bd ≤ (n : ℝ) ^ 3 + Bd ^ 4 := nB_le8 hB
  have e3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := n2_le_n3
  have e4 : (n : ℝ) ≤ (n : ℝ) ^ 3 := n_le_n3
  have e5 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg n) 3
  have e6 : (0 : ℝ) ≤ Bd ^ 4 := by positivity
  have e7 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have e8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  linarith

set_option maxHeartbeats 1000000 in
/-- **The order-eight induction step, as pure arithmetic.** -/
lemma step_eight {n : ℕ} {Bd a b m3 m5 m6 m8 M4 M5 M6 M8 : ℝ}
    (hB : 1 ≤ Bd) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM4 : M4 ≤ 3 * (1 + a + b) ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))) (hM4n : 0 ≤ M4)
    (hM6 : M6 ≤ 40 * (1 + a + b) ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) (hM6n : 0 ≤ M6)
    (hM5 : |M5| ≤ (M4 + M6) / 2)
    (hm3 : |m3| ≤ 1 + a + b) (hm5 : |m5| ≤ Bd * (1 + a + b))
    (hm6 : |m6| ≤ Bd ^ 2 * (1 + a + b)) (hm8 : |m8| ≤ Bd ^ 4 * (1 + a + b))
    (hM8 : M8 ≤ 2400 * (1 + a + b) ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) :
    M8 + 28 * a * M6 + 56 * m3 * M5 + 70 * b * M4 + 56 * (n : ℝ) * m5 * m3
        + 28 * (n : ℝ) * m6 * a + m8
      ≤ 2400 * (1 + a + b) ^ 4 * (((n : ℝ) + 1) ^ 4 + ((n : ℝ) + 1) * Bd ^ 4) := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + a + b := ⟨_, rfl⟩
  rw [← hAdef] at hM4 hM6 hm3 hm5 hm6 hm8 hM8 ⊢
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have haA : a ≤ A := by rw [hAdef]; linarith
  have hbA : b ≤ A := by rw [hAdef]; linarith
  have hB0 : (0 : ℝ) ≤ Bd := le_trans zero_le_one hB
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hP2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 + (n : ℝ) := by positivity
  have hP3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2 := by positivity
  have hA34 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right₀ hA1 (by norm_num)
  have hA24 : A ^ 2 ≤ A ^ 4 := pow_le_pow_right₀ hA1 (by norm_num)
  have hA14 : A ≤ A ^ 4 := by
    have := pow_le_pow_right₀ hA1 (show 1 ≤ 4 by norm_num); simpa using this
  have hA40 : (0 : ℝ) ≤ A ^ 4 := by positivity
  have g34 : A ^ 3 * ((n : ℝ) ^ 2 + (n : ℝ)) ≤ A ^ 4 * ((n : ℝ) ^ 2 + (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hA34 hP2
  have g24 : A ^ 2 * ((n : ℝ) * Bd) ≤ A ^ 4 * ((n : ℝ) * Bd) :=
    mul_le_mul_of_nonneg_right hA24 (mul_nonneg hn0 hB0)
  have g24' : A ^ 2 * ((n : ℝ) * Bd ^ 2) ≤ A ^ 4 * ((n : ℝ) * Bd ^ 2) :=
    mul_le_mul_of_nonneg_right hA24 (mul_nonneg hn0 (sq_nonneg Bd))
  have g14 : A * Bd ^ 4 ≤ A ^ 4 * Bd ^ 4 :=
    mul_le_mul_of_nonneg_right hA14 (by positivity)
  -- term 1
  have t1 : 28 * a * M6 ≤ 1120 * A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) := by
    have h : a * M6 ≤ A * (40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) :=
      mul_le_mul haA hM6 hM6n hA0
    have e : A * (40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
        = 40 * A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) := by ring
    rw [e] at h; linarith
  -- term 2
  have t2 : 56 * m3 * M5
      ≤ 84 * A ^ 4 * ((n : ℝ) ^ 2 + (n : ℝ))
        + 1120 * A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) := by
    have h1 : m3 * M5 ≤ |m3| * |M5| := by
      calc m3 * M5 ≤ |m3 * M5| := le_abs_self _
        _ = |m3| * |M5| := abs_mul _ _
    have h2 : |m3| * |M5| ≤ A * ((M4 + M6) / 2) := mul_le_mul hm3 hM5 (abs_nonneg _) hA0
    have h3 : M4 + M6 ≤ 3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))
        + 40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) := by linarith
    have h4 : A * ((M4 + M6) / 2)
        ≤ A * ((3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))
            + 40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) / 2) := by
      have := mul_le_mul_of_nonneg_left h3 hA0
      linarith
    have h5 : A * ((3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))
            + 40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) / 2)
        = (3 / 2) * (A ^ 3 * ((n : ℝ) ^ 2 + (n : ℝ)))
          + 20 * (A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) := by ring
    rw [h5] at h4
    linarith
  -- term 3
  have t3 : 70 * b * M4 ≤ 210 * A ^ 4 * ((n : ℝ) ^ 2 + (n : ℝ)) := by
    have h : b * M4 ≤ A * (3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))) :=
      mul_le_mul hbA hM4 hM4n hA0
    have e : A * (3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))
        = 3 * (A ^ 3 * ((n : ℝ) ^ 2 + (n : ℝ))) := by ring
    rw [e] at h; linarith
  -- term 4
  have t4 : 56 * (n : ℝ) * m5 * m3 ≤ 56 * (A ^ 4 * ((n : ℝ) * Bd)) := by
    have h1 : m5 * m3 ≤ |m5| * |m3| := by
      calc m5 * m3 ≤ |m5 * m3| := le_abs_self _
        _ = |m5| * |m3| := abs_mul _ _
    have h2 : |m5| * |m3| ≤ (Bd * A) * A := mul_le_mul hm5 hm3 (abs_nonneg _) (by positivity)
    have h3 : (n : ℝ) * (m5 * m3) ≤ (n : ℝ) * ((Bd * A) * A) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hn0
    nlinarith [h3, g24]
  -- term 5
  have t5 : 28 * (n : ℝ) * m6 * a ≤ 28 * (A ^ 4 * ((n : ℝ) * Bd ^ 2)) := by
    have h1 : m6 * a ≤ |m6| * a := by
      have h := le_abs_self m6
      exact mul_le_mul_of_nonneg_right h ha
    have h2 : |m6| * a ≤ (Bd ^ 2 * A) * A := mul_le_mul hm6 haA ha (by positivity)
    have h3 : (n : ℝ) * (m6 * a) ≤ (n : ℝ) * ((Bd ^ 2 * A) * A) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hn0
    nlinarith [h3, g24']
  -- term 6
  have t6 : m8 ≤ A ^ 4 * Bd ^ 4 := by
    have h : m8 ≤ Bd ^ 4 * A := le_trans (le_abs_self _) hm8
    linarith [g14]
  -- assemble
  have hled := step_eight_ledger (n := n) hB
  have hmul := mul_le_mul_of_nonneg_left hled hA40
  linarith [t1, t2, t3, t4, t5, t6, hM8, hmul]

/-- The pure `(n, B)` ledger of the order-ten step. -/
lemma step_ten_ledger {n : ℕ} {Bd : ℝ} (hB : 1 ≤ Bd) :
    108000 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4) + 2400 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)
        + 144000 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)
        + 8400 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)
        + 378 * (Bd * ((n : ℝ) ^ 2 + (n : ℝ)))
        + 5040 * (Bd * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
        + 630 * (Bd ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))
        + 120 * ((n : ℝ) * Bd ^ 3) + 45 * ((n : ℝ) * Bd ^ 4) + Bd ^ 6
      ≤ 540000 * (5 * (n : ℝ) ^ 4 + 10 * (n : ℝ) ^ 3 + 10 * (n : ℝ) ^ 2 + 5 * (n : ℝ)
          + 1 + Bd ^ 6) := by
  have e1 : (n : ℝ) * Bd ^ 4 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := nB4_le10
  have e2 : (n : ℝ) * Bd ^ 2 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := nB2_le10 hB
  have e3 : (n : ℝ) * Bd ^ 3 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := nB3_le10 hB
  have e4 : Bd * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := Bn3_le10 hB
  have e5 : Bd * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := Bn2_le10 hB
  have e6 : Bd * (n : ℝ) ≤ (n : ℝ) ^ 4 + Bd ^ 6 := Bn_le10 hB
  have e7 : Bd ^ 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 + Bd ^ 6 := B2n2_le10
  have e8 : Bd ^ 2 * (n : ℝ) ≤ (n : ℝ) ^ 4 + Bd ^ 6 := B2n_le10
  have e9 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := n3_le_n4
  have e10 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := n2_le_n4
  have e11 : (n : ℝ) ≤ (n : ℝ) ^ 4 := n_le_n4
  have e12 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg n) 4
  have e13 : (0 : ℝ) ≤ Bd ^ 6 := by positivity
  have e14 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have e15 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have e16 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg n) 3
  nlinarith [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16]

set_option maxHeartbeats 2000000 in
/-- **The order-ten induction step, as pure arithmetic.** -/
lemma step_ten {n : ℕ} {Bd a b m3 m5 m6 m7 m8 m10 M4 M5 M6 M7 M8 M10 : ℝ}
    (hB : 1 ≤ Bd) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM4 : M4 ≤ 3 * (1 + a + b) ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))) (hM4n : 0 ≤ M4)
    (hM6 : M6 ≤ 40 * (1 + a + b) ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) (hM6n : 0 ≤ M6)
    (hM8 : M8 ≤ 2400 * (1 + a + b) ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) (hM8n : 0 ≤ M8)
    (hM5 : |M5| ≤ (M4 + M6) / 2) (hM7 : |M7| ≤ (M6 + M8) / 2)
    (hm3 : |m3| ≤ 1 + a + b) (hm5 : |m5| ≤ Bd * (1 + a + b))
    (hm6 : |m6| ≤ Bd ^ 2 * (1 + a + b)) (hm7 : |m7| ≤ Bd ^ 3 * (1 + a + b))
    (hm8 : |m8| ≤ Bd ^ 4 * (1 + a + b)) (hm10 : |m10| ≤ Bd ^ 6 * (1 + a + b))
    (hM10 : M10 ≤ 540000 * (1 + a + b) ^ 5 * ((n : ℝ) ^ 5 + (n : ℝ) * Bd ^ 6)) :
    M10 + 45 * a * M8 + 120 * m3 * M7 + 210 * b * M6 + 252 * m5 * M5 + 210 * m6 * M4
        + 120 * (n : ℝ) * m7 * m3 + 45 * (n : ℝ) * m8 * a + m10
      ≤ 540000 * (1 + a + b) ^ 5 * (((n : ℝ) + 1) ^ 5 + ((n : ℝ) + 1) * Bd ^ 6) := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + a + b := ⟨_, rfl⟩
  rw [← hAdef] at hM4 hM6 hM8 hm3 hm5 hm6 hm7 hm8 hm10 hM10 ⊢
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have haA : a ≤ A := by rw [hAdef]; linarith
  have hbA : b ≤ A := by rw [hAdef]; linarith
  have hB0 : (0 : ℝ) ≤ Bd := le_trans zero_le_one hB
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hP2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 + (n : ℝ) := by positivity
  have hP3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2 := by positivity
  have hA45 : A ^ 4 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
  have hA35 : A ^ 3 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
  have hA25 : A ^ 2 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
  have hA15 : A ≤ A ^ 5 := by
    have := pow_le_pow_right₀ hA1 (show 1 ≤ 5 by norm_num); simpa using this
  have hA50 : (0 : ℝ) ≤ A ^ 5 := by positivity
  have g45 : A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)
      ≤ A ^ 5 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) := mul_le_mul_of_nonneg_right hA45 hP3
  have g35 : A ^ 3 * (Bd * ((n : ℝ) ^ 2 + (n : ℝ)))
      ≤ A ^ 5 * (Bd * ((n : ℝ) ^ 2 + (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hA35 (mul_nonneg hB0 hP2)
  have g45' : A ^ 4 * (Bd * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
      ≤ A ^ 5 * (Bd * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) :=
    mul_le_mul_of_nonneg_right hA45 (mul_nonneg hB0 hP3)
  have g35' : A ^ 3 * (Bd ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))
      ≤ A ^ 5 * (Bd ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hA35 (mul_nonneg (sq_nonneg Bd) hP2)
  have g25 : A ^ 2 * ((n : ℝ) * Bd ^ 3) ≤ A ^ 5 * ((n : ℝ) * Bd ^ 3) :=
    mul_le_mul_of_nonneg_right hA25 (by positivity)
  have g25' : A ^ 2 * ((n : ℝ) * Bd ^ 4) ≤ A ^ 5 * ((n : ℝ) * Bd ^ 4) :=
    mul_le_mul_of_nonneg_right hA25 (by positivity)
  have g15 : A * Bd ^ 6 ≤ A ^ 5 * Bd ^ 6 := mul_le_mul_of_nonneg_right hA15 (by positivity)
  -- term 1
  have t1 : 45 * a * M8 ≤ 108000 * (A ^ 5 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) := by
    have h : a * M8 ≤ A * (2400 * A ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) :=
      mul_le_mul haA hM8 hM8n hA0
    have e : A * (2400 * A ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4))
        = 2400 * (A ^ 5 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) := by ring
    rw [e] at h; linarith
  -- term 2
  have t2 : 120 * m3 * M7 ≤ 2400 * (A ^ 5 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
      + 144000 * (A ^ 5 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) := by
    have h1 : m3 * M7 ≤ |m3| * |M7| := by
      calc m3 * M7 ≤ |m3 * M7| := le_abs_self _
        _ = |m3| * |M7| := abs_mul _ _
    have h2 : |m3| * |M7| ≤ A * ((M6 + M8) / 2) := mul_le_mul hm3 hM7 (abs_nonneg _) hA0
    have h3 : M6 + M8 ≤ 40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)
        + 2400 * A ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hA0
    have h5 : A * (40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)
        + 2400 * A ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4))
        = 40 * (A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
          + 2400 * (A ^ 5 * ((n : ℝ) ^ 4 + (n : ℝ) * Bd ^ 4)) := by ring
    rw [h5] at h4
    linarith
  -- term 3
  have t3 : 210 * b * M6 ≤ 8400 * (A ^ 5 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) := by
    have h : b * M6 ≤ A * (40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) :=
      mul_le_mul hbA hM6 hM6n hA0
    have e : A * (40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
        = 40 * (A ^ 4 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2)) := by ring
    rw [e] at h; linarith
  -- term 4
  have t4 : 252 * m5 * M5 ≤ 378 * (A ^ 5 * (Bd * ((n : ℝ) ^ 2 + (n : ℝ))))
      + 5040 * (A ^ 5 * (Bd * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))) := by
    have h1 : m5 * M5 ≤ |m5| * |M5| := by
      calc m5 * M5 ≤ |m5 * M5| := le_abs_self _
        _ = |m5| * |M5| := abs_mul _ _
    have h2 : |m5| * |M5| ≤ (Bd * A) * ((M4 + M6) / 2) :=
      mul_le_mul hm5 hM5 (abs_nonneg _) (by positivity)
    have h3 : M4 + M6 ≤ 3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))
        + 40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ Bd * A by positivity)
    have h5 : Bd * A * (3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))
        + 40 * A ^ 3 * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))
        = 3 * (A ^ 3 * (Bd * ((n : ℝ) ^ 2 + (n : ℝ))))
          + 40 * (A ^ 4 * (Bd * ((n : ℝ) ^ 3 + (n : ℝ) * Bd ^ 2))) := by ring
    rw [h5] at h4
    linarith
  -- term 5
  have t5 : 210 * m6 * M4 ≤ 630 * (A ^ 5 * (Bd ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))) := by
    have h1 : m6 * M4 ≤ |m6| * M4 := mul_le_mul_of_nonneg_right (le_abs_self _) hM4n
    have h2 : |m6| * M4 ≤ (Bd ^ 2 * A) * (3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ))) :=
      mul_le_mul hm6 hM4 hM4n (by positivity)
    have e : (Bd ^ 2 * A) * (3 * A ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))
        = 3 * (A ^ 3 * (Bd ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))) := by ring
    rw [e] at h2
    linarith
  -- term 6
  have t6 : 120 * (n : ℝ) * m7 * m3 ≤ 120 * (A ^ 5 * ((n : ℝ) * Bd ^ 3)) := by
    have h1 : m7 * m3 ≤ |m7| * |m3| := by
      calc m7 * m3 ≤ |m7 * m3| := le_abs_self _
        _ = |m7| * |m3| := abs_mul _ _
    have h2 : |m7| * |m3| ≤ (Bd ^ 3 * A) * A := mul_le_mul hm7 hm3 (abs_nonneg _) (by positivity)
    have h3 : (n : ℝ) * (m7 * m3) ≤ (n : ℝ) * ((Bd ^ 3 * A) * A) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hn0
    have e : (n : ℝ) * ((Bd ^ 3 * A) * A) = A ^ 2 * ((n : ℝ) * Bd ^ 3) := by ring
    rw [e] at h3
    linarith
  -- term 7
  have t7 : 45 * (n : ℝ) * m8 * a ≤ 45 * (A ^ 5 * ((n : ℝ) * Bd ^ 4)) := by
    have h1 : m8 * a ≤ |m8| * a := mul_le_mul_of_nonneg_right (le_abs_self _) ha
    have h2 : |m8| * a ≤ (Bd ^ 4 * A) * A := mul_le_mul hm8 haA ha (by positivity)
    have h3 : (n : ℝ) * (m8 * a) ≤ (n : ℝ) * ((Bd ^ 4 * A) * A) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hn0
    have e : (n : ℝ) * ((Bd ^ 4 * A) * A) = A ^ 2 * ((n : ℝ) * Bd ^ 4) := by ring
    rw [e] at h3
    linarith
  -- term 8
  have t8 : m10 ≤ A ^ 5 * Bd ^ 6 := by
    have h : m10 ≤ Bd ^ 6 * A := le_trans (le_abs_self _) hm10
    linarith [g15]
  have hled := step_ten_ledger (n := n) hB
  have hmul := mul_le_mul_of_nonneg_left hled hA50
  linarith [t1, t2, t3, t4, t5, t6, t7, t8, hM10, hmul]


/-! ### stubs of the Edgeworth prerequisites -/

lemma integral_pi_sum_moments (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    (∫ y : Fin n → ℝ, (∑ i, V (y i)) ∂(Measure.pi fun _ : Fin n => F)) = 0 ∧
      (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 2 ∂(Measure.pi fun _ : Fin n => F))
        = n * ∫ x, V x ^ 2 ∂F ∧
      (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 4 ∂(Measure.pi fun _ : Fin n => F))
        ≤ n * (∫ x, V x ^ 4 ∂F) + 3 * n ^ 2 * (∫ x, V x ^ 2 ∂F) ^ 2 := sorry

lemma integral_pi_sum_pow_succ (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (n p : ℕ) :
    ∫ y : Fin (n + 1) → ℝ, (∑ i, V (y i)) ^ p ∂(Measure.pi fun _ : Fin (n + 1) => F)
      = ∑ k ∈ Finset.range (p + 1), (p.choose k : ℝ) * (∫ x, V x ^ k ∂F)
          * ∫ z : Fin n → ℝ, (∑ i, V (z i)) ^ (p - k) ∂(Measure.pi fun _ : Fin n => F) := sorry

lemma integral_pi_sum_pow_three (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 3 ∂(Measure.pi fun _ : Fin n => F)
      = (n : ℝ) * ∫ x, V x ^ 3 ∂F := sorry

lemma integral_pi_sum_pow_six_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 6 ∂(Measure.pi fun _ : Fin n => F)
      ≤ (n : ℝ) * (∫ x, V x ^ 6 ∂F)
        + 15 * (n : ℝ) ^ 2 * (∫ x, V x ^ 2 ∂F) * (∫ x, V x ^ 4 ∂F)
        + 10 * (n : ℝ) ^ 2 * (∫ x, V x ^ 3 ∂F) ^ 2
        + 15 * (n : ℝ) ^ 3 * (∫ x, V x ^ 2 ∂F) ^ 3 := sorry

lemma integrable_pow_of_bounded {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {W : α → ℝ} (hW : Measurable W) {D : ℝ} (hWb : ∀ z, |W z| ≤ D)
    (k : ℕ) : Integrable (fun z => W z ^ k) ν := sorry


/-! ### Pointwise AM-GM for the odd powers -/

lemma two_mul_abs_pow_three_le (s : ℝ) : 2 * |s ^ 3| ≤ s ^ 2 + s ^ 4 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e2 : s ^ 2 = |s| ^ 2 := h.symm
  have e4 : s ^ 4 = (|s| ^ 2) ^ 2 := by rw [h]; ring
  rw [abs_pow, e2, e4]
  nlinarith [sq_nonneg (|s| - |s| ^ 2), abs_nonneg s]

lemma two_mul_abs_pow_five_le (s : ℝ) : 2 * |s ^ 5| ≤ s ^ 4 + s ^ 6 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e4 : s ^ 4 = (|s| ^ 2) ^ 2 := by rw [h]; ring
  have e6 : s ^ 6 = (|s| ^ 2) ^ 3 := by rw [h]; ring
  rw [abs_pow, e4, e6]
  nlinarith [sq_nonneg (|s| ^ 2 - |s| ^ 3), abs_nonneg s]

lemma two_mul_abs_pow_seven_le (s : ℝ) : 2 * |s ^ 7| ≤ s ^ 6 + s ^ 8 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e6 : s ^ 6 = (|s| ^ 2) ^ 3 := by rw [h]; ring
  have e8 : s ^ 8 = (|s| ^ 2) ^ 4 := by rw [h]; ring
  rw [abs_pow, e6, e8]
  nlinarith [sq_nonneg (|s| ^ 3 - |s| ^ 4), abs_nonneg s]

lemma two_mul_abs_pow_nine_le (s : ℝ) : 2 * |s ^ 9| ≤ s ^ 8 + s ^ 10 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e8 : s ^ 8 = (|s| ^ 2) ^ 4 := by rw [h]; ring
  have e10 : s ^ 10 = (|s| ^ 2) ^ 5 := by rw [h]; ring
  rw [abs_pow, e8, e10]
  nlinarith [sq_nonneg (|s| ^ 4 - |s| ^ 5), abs_nonneg s]

/-! ### The absolute moments of the summand -/

/-- `|∫ Vᵏ| ≤ B^{k−4} ∫ V⁴` for `k ≥ 4`: the truncation level pays for every power above the
fourth. -/
lemma abs_integral_pow_le_of_bounded (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) {k : ℕ} (hk : 4 ≤ k) :
    |∫ x, V x ^ k ∂F| ≤ B ^ (k - 4) * ∫ x, V x ^ 4 ∂F := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hpt : ∀ x, |V x ^ k| ≤ B ^ (k - 4) * V x ^ 4 := by
    intro x
    have hsplit : |V x| ^ k = |V x| ^ (k - 4) * |V x| ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have h1 : |V x| ^ (k - 4) ≤ B ^ (k - 4) := pow_le_pow_left₀ (abs_nonneg _) (hB x) _
    have h2 : |V x| ^ 4 = V x ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [abs_pow, hsplit, h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hI1 : Integrable (fun x => |V x ^ k|) F := (integrable_pow_of_bounded F hV hB k).abs
  have hI2 : Integrable (fun x => B ^ (k - 4) * V x ^ 4) F :=
    (integrable_pow_of_bounded F hV hB 4).const_mul _
  calc |∫ x, V x ^ k ∂F| ≤ ∫ x, |V x ^ k| ∂F := abs_integral_le_integral_abs
    _ ≤ ∫ x, B ^ (k - 4) * V x ^ 4 ∂F := integral_mono hI1 hI2 hpt
    _ = B ^ (k - 4) * ∫ x, V x ^ 4 ∂F := integral_const_mul _ _

/-- `|∫ V³| ≤ (∫ V² + ∫ V⁴)/2` — the third moment costs no power of the truncation level. -/
lemma abs_integral_pow_three_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) :
    |∫ x, V x ^ 3 ∂F| ≤ ((∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) / 2 := by
  have hI1 : Integrable (fun x => |V x ^ 3|) F := (integrable_pow_of_bounded F hV hB 3).abs
  have hI2 : Integrable (fun x => (V x ^ 2 + V x ^ 4) / 2) F :=
    (((integrable_pow_of_bounded F hV hB 2).add
      (integrable_pow_of_bounded F hV hB 4))).div_const 2
  have h : ∫ x, |V x ^ 3| ∂F ≤ ∫ x, (V x ^ 2 + V x ^ 4) / 2 ∂F :=
    integral_mono hI1 hI2 fun x => by linarith [two_mul_abs_pow_three_le (V x)]
  have he : ∫ x, (V x ^ 2 + V x ^ 4) / 2 ∂F = ((∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) / 2 := by
    rw [integral_div, integral_add (integrable_pow_of_bounded F hV hB 2)
      (integrable_pow_of_bounded F hV hB 4)]
  calc |∫ x, V x ^ 3 ∂F| ≤ ∫ x, |V x ^ 3| ∂F := abs_integral_le_integral_abs
    _ ≤ _ := h
    _ = _ := he


/-! ### The odd moments of the sum, sandwiched between the neighbouring even ones -/

lemma abs_integral_odd_aux {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {S : α → ℝ} (hS : Measurable S) {D : ℝ} (hSb : ∀ z, |S z| ≤ D)
    {j i k : ℕ} (hpt : ∀ s : ℝ, 2 * |s ^ j| ≤ s ^ i + s ^ k) :
    |∫ z, S z ^ j ∂ν| ≤ ((∫ z, S z ^ i ∂ν) + ∫ z, S z ^ k ∂ν) / 2 := by
  have hI1 : Integrable (fun z => |S z ^ j|) ν := (integrable_pow_of_bounded ν hS hSb j).abs
  have hIi := integrable_pow_of_bounded ν hS hSb i
  have hIk := integrable_pow_of_bounded ν hS hSb k
  have hI2 : Integrable (fun z => (S z ^ i + S z ^ k) / 2) ν := (hIi.add hIk).div_const 2
  have h : ∫ z, |S z ^ j| ∂ν ≤ ∫ z, (S z ^ i + S z ^ k) / 2 ∂ν :=
    integral_mono hI1 hI2 fun z => by linarith [hpt (S z)]
  have he : ∫ z, (S z ^ i + S z ^ k) / 2 ∂ν = ((∫ z, S z ^ i ∂ν) + ∫ z, S z ^ k ∂ν) / 2 := by
    rw [integral_div, integral_add hIi hIk]
  calc |∫ z, S z ^ j ∂ν| ≤ ∫ z, |S z ^ j| ∂ν := abs_integral_le_integral_abs
    _ ≤ _ := h
    _ = _ := he

/-! ### The order-four and order-six bounds in the graded shape -/

lemma integral_pi_sum_pow_four_A (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 4 ∂(Measure.pi fun _ : Fin n => F)
      ≤ 3 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)) := by
  obtain ⟨-, -, h4⟩ := integral_pi_sum_moments F hV hB hV0 n
  have ha : (0 : ℝ) ≤ ∫ x, V x ^ 2 ∂F := integral_nonneg fun x => by positivity
  have hb : (0 : ℝ) ≤ ∫ x, V x ^ 4 ∂F := integral_nonneg fun x => by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = ∫ x, V x ^ 2 ∂F := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = ∫ x, V x ^ 4 ∂F := ⟨_, rfl⟩
  rw [← hadef, ← hbdef] at h4 ⊢
  rw [← hadef] at ha
  rw [← hbdef] at hb
  have h1 : a ^ 2 ≤ (1 + a + b) ^ 2 := by nlinarith
  have h2 : b ≤ (1 + a + b) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 3 * (n : ℝ) ^ 2 by positivity),
    mul_le_mul_of_nonneg_left h2 hn, sq_nonneg (1 + a + b)]

lemma integral_pi_sum_pow_six_A (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B) (hV0 : ∫ x, V x ∂F = 0)
    (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 6 ∂(Measure.pi fun _ : Fin n => F)
      ≤ 40 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 3
          * ((n : ℝ) ^ 3 + (n : ℝ) * B ^ 2) := by
  have h6 := integral_pi_sum_pow_six_le F hV hB hV0 n
  have hm6 : |∫ x, V x ^ 6 ∂F| ≤ B ^ 2 * ∫ x, V x ^ 4 ∂F := by
    have := abs_integral_pow_le_of_bounded F hV hB (k := 6) (by norm_num)
    simpa using this
  have hm3 := abs_integral_pow_three_le F hV hB
  have ha : (0 : ℝ) ≤ ∫ x, V x ^ 2 ∂F := integral_nonneg fun x => by positivity
  have hb : (0 : ℝ) ≤ ∫ x, V x ^ 4 ∂F := integral_nonneg fun x => by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := n2_le_n3
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = ∫ x, V x ^ 2 ∂F := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = ∫ x, V x ^ 4 ∂F := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ∫ x, V x ^ 3 ∂F := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = ∫ x, V x ^ 6 ∂F := ⟨_, rfl⟩
  rw [← hadef, ← hbdef, ← hcdef, ← hddef] at h6
  rw [← hddef, ← hbdef] at hm6
  rw [← hcdef, ← hadef, ← hbdef] at hm3
  rw [← hadef] at ha
  rw [← hbdef] at hb
  rw [← hadef, ← hbdef]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + a + b := ⟨_, rfl⟩
  rw [← hAdef]
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have haA : a ≤ A := by rw [hAdef]; linarith
  have hbA : b ≤ A := by rw [hAdef]; linarith
  have hA23 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA1 (by norm_num)
  have hA13 : A ≤ A ^ 3 := by
    have := pow_le_pow_right₀ hA1 (show 1 ≤ 3 by norm_num); simpa using this
  have hA30 : (0 : ℝ) ≤ A ^ 3 := by positivity
  -- the four terms
  have t1 : (n : ℝ) * d ≤ A ^ 3 * ((n : ℝ) * B ^ 2) := by
    have hd : d ≤ B ^ 2 * b := le_trans (le_abs_self _) hm6
    have h1 : (n : ℝ) * d ≤ (n : ℝ) * (B ^ 2 * b) := mul_le_mul_of_nonneg_left hd hn
    have h2 : (n : ℝ) * (B ^ 2 * b) ≤ (n : ℝ) * (B ^ 2 * A) := by
      have : B ^ 2 * b ≤ B ^ 2 * A := mul_le_mul_of_nonneg_left hbA (sq_nonneg B)
      exact mul_le_mul_of_nonneg_left this hn
    have h3 : (n : ℝ) * (B ^ 2 * A) ≤ A ^ 3 * ((n : ℝ) * B ^ 2) := by
      have : A * ((n : ℝ) * B ^ 2) ≤ A ^ 3 * ((n : ℝ) * B ^ 2) :=
        mul_le_mul_of_nonneg_right hA13 (by positivity)
      linarith
    linarith
  have t2 : 15 * (n : ℝ) ^ 2 * a * b ≤ 15 * (A ^ 3 * (n : ℝ) ^ 3) := by
    have h1 : a * b ≤ A * A := mul_le_mul haA hbA hb hA0
    have h2 : (n : ℝ) ^ 2 * (a * b) ≤ (n : ℝ) ^ 2 * (A * A) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have h3 : A ^ 2 * (n : ℝ) ^ 2 ≤ A ^ 3 * (n : ℝ) ^ 3 := by
      have e1 : A ^ 2 * (n : ℝ) ^ 2 ≤ A ^ 3 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hA23 (sq_nonneg _)
      have e2 : A ^ 3 * (n : ℝ) ^ 2 ≤ A ^ 3 * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hn23 hA30
      linarith
    nlinarith [h2, h3]
  have t3 : 10 * (n : ℝ) ^ 2 * c ^ 2 ≤ 10 * (A ^ 3 * (n : ℝ) ^ 3) := by
    have hc : |c| ≤ A := by rw [hAdef]; linarith [abs_nonneg c]
    have h1 : c ^ 2 ≤ A ^ 2 := by
      have := sq_abs c
      nlinarith [abs_nonneg c, hc]
    have h2 : (n : ℝ) ^ 2 * c ^ 2 ≤ (n : ℝ) ^ 2 * A ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have h3 : A ^ 2 * (n : ℝ) ^ 2 ≤ A ^ 3 * (n : ℝ) ^ 3 := by
      have e1 : A ^ 2 * (n : ℝ) ^ 2 ≤ A ^ 3 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hA23 (sq_nonneg _)
      have e2 : A ^ 3 * (n : ℝ) ^ 2 ≤ A ^ 3 * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hn23 hA30
      linarith
    nlinarith [h2, h3]
  have t4 : 15 * (n : ℝ) ^ 3 * a ^ 3 ≤ 15 * (A ^ 3 * (n : ℝ) ^ 3) := by
    have h1 : a ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ ha haA 3
    nlinarith [mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 15 * (n:ℝ)^3 by positivity)]
  have hfin : (0 : ℝ) ≤ A ^ 3 * ((n : ℝ) * B ^ 2) := by positivity
  nlinarith [h6, t1, t2, t3, t4, hfin]


set_option maxHeartbeats 1000000 in
lemma integral_pi_sum_pow_eight_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B)
    (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 8 ∂(Measure.pi fun _ : Fin n => F)
      ≤ 2400 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 4
          * ((n : ℝ) ^ 4 + (n : ℝ) * B ^ 4) := by
  have ha : (0 : ℝ) ≤ ∫ x, V x ^ 2 ∂F := integral_nonneg fun x => by positivity
  have hb : (0 : ℝ) ≤ ∫ x, V x ^ 4 ∂F := integral_nonneg fun x => by positivity
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hm3' : |∫ x, V x ^ 3 ∂F| ≤ 1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F := by
    have := abs_integral_pow_three_le F hV hB
    linarith
  have hm5' : |∫ x, V x ^ 5 ∂F| ≤ B * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 5) (by norm_num)
    have hB1' : B ^ (5 - 4) = B := by norm_num
    rw [hB1'] at h
    nlinarith [h, hB0, ha]
  have hm6' : |∫ x, V x ^ 6 ∂F| ≤ B ^ 2 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 6) (by norm_num)
    have hB2' : B ^ (6 - 4) = B ^ 2 := by norm_num
    rw [hB2'] at h
    nlinarith [h, sq_nonneg B, ha]
  have hm8' : |∫ x, V x ^ 8 ∂F| ≤ B ^ 4 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 8) (by norm_num)
    have hB4' : B ^ (8 - 4) = B ^ 4 := by norm_num
    rw [hB4'] at h
    nlinarith [h, pow_nonneg hB0 4, ha]
  induction n with
  | zero => simp
  | succ n ih =>
    have hsumm : Measurable fun z : Fin n → ℝ => ∑ i, V (z i) :=
      Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)
    have hsumb : ∀ z : Fin n → ℝ, |∑ i, V (z i)| ≤ (n : ℝ) * B := by
      intro z
      calc |∑ i, V (z i)| ≤ ∑ _i : Fin n, B :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB (z i))
        _ = (n : ℝ) * B := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    obtain ⟨h1, h2, -⟩ := integral_pi_sum_moments F hV hB hV0 n
    have h3 := integral_pi_sum_pow_three F hV hB hV0 n
    have hM4 := integral_pi_sum_pow_four_A F hV hB hV0 n
    have hM6 := integral_pi_sum_pow_six_A F hV hB hB1 hV0 n
    have hM4n : (0 : ℝ) ≤ ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 4
        ∂(Measure.pi fun _ : Fin n => F) := integral_nonneg fun y => by positivity
    have hM6n : (0 : ℝ) ≤ ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 6
        ∂(Measure.pi fun _ : Fin n => F) := integral_nonneg fun y => by positivity
    have hM5 := abs_integral_odd_aux (Measure.pi fun _ : Fin n => F) hsumm hsumb
      two_mul_abs_pow_five_le
    have hm0 : (∫ x, V x ^ 0 ∂F) = 1 := by simp
    have hm1 : (∫ x, V x ^ 1 ∂F) = 0 := by simpa using hV0
    have hM0 : (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 0
        ∂(Measure.pi fun _ : Fin n => F)) = 1 := by simp
    have hM1 : (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 1
        ∂(Measure.pi fun _ : Fin n => F)) = 0 := by simpa using h1
    have hstep := step_eight (n := n) (Bd := B) (a := ∫ x, V x ^ 2 ∂F)
      (b := ∫ x, V x ^ 4 ∂F) (m3 := ∫ x, V x ^ 3 ∂F) (m5 := ∫ x, V x ^ 5 ∂F)
      (m6 := ∫ x, V x ^ 6 ∂F) (m8 := ∫ x, V x ^ 8 ∂F)
      hB1 ha hb hM4 hM4n hM6 hM6n hM5 hm3' hm5' hm6' hm8' ih
    rw [integral_pi_sum_pow_succ F hV hB n 8]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [Nat.choose, hm0, hm1, hM0, hM1, hV0, h1, h2, h3]
    linarith [hstep]


set_option maxHeartbeats 2000000 in
lemma integral_pi_sum_pow_ten_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B)
    (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 10 ∂(Measure.pi fun _ : Fin n => F)
      ≤ 540000 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 5
          * ((n : ℝ) ^ 5 + (n : ℝ) * B ^ 6) := by
  have ha : (0 : ℝ) ≤ ∫ x, V x ^ 2 ∂F := integral_nonneg fun x => by positivity
  have hb : (0 : ℝ) ≤ ∫ x, V x ^ 4 ∂F := integral_nonneg fun x => by positivity
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hm3' : |∫ x, V x ^ 3 ∂F| ≤ 1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F := by
    have := abs_integral_pow_three_le F hV hB
    linarith
  have hm5' : |∫ x, V x ^ 5 ∂F| ≤ B * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 5) (by norm_num)
    have hB1' : B ^ (5 - 4) = B := by norm_num
    rw [hB1'] at h
    nlinarith [h, hB0, ha]
  have hm6' : |∫ x, V x ^ 6 ∂F| ≤ B ^ 2 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 6) (by norm_num)
    have hB2' : B ^ (6 - 4) = B ^ 2 := by norm_num
    rw [hB2'] at h
    nlinarith [h, sq_nonneg B, ha]
  have hm7' : |∫ x, V x ^ 7 ∂F| ≤ B ^ 3 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 7) (by norm_num)
    have hB3' : B ^ (7 - 4) = B ^ 3 := by norm_num
    rw [hB3'] at h
    nlinarith [h, pow_nonneg hB0 3, ha]
  have hm8' : |∫ x, V x ^ 8 ∂F| ≤ B ^ 4 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 8) (by norm_num)
    have hB4' : B ^ (8 - 4) = B ^ 4 := by norm_num
    rw [hB4'] at h
    nlinarith [h, pow_nonneg hB0 4, ha]
  have hm10' : |∫ x, V x ^ 10 ∂F| ≤ B ^ 6 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) := by
    have h := abs_integral_pow_le_of_bounded F hV hB (k := 10) (by norm_num)
    have hB6' : B ^ (10 - 4) = B ^ 6 := by norm_num
    rw [hB6'] at h
    nlinarith [h, pow_nonneg hB0 6, ha]
  induction n with
  | zero => simp
  | succ n ih =>
    have hsumm : Measurable fun z : Fin n → ℝ => ∑ i, V (z i) :=
      Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)
    have hsumb : ∀ z : Fin n → ℝ, |∑ i, V (z i)| ≤ (n : ℝ) * B := by
      intro z
      calc |∑ i, V (z i)| ≤ ∑ _i : Fin n, B :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB (z i))
        _ = (n : ℝ) * B := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    obtain ⟨h1, h2, -⟩ := integral_pi_sum_moments F hV hB hV0 n
    have h3 := integral_pi_sum_pow_three F hV hB hV0 n
    have hM4 := integral_pi_sum_pow_four_A F hV hB hV0 n
    have hM6 := integral_pi_sum_pow_six_A F hV hB hB1 hV0 n
    have hM8 := integral_pi_sum_pow_eight_le F hV hB hB1 hV0 n
    have hM4n : (0 : ℝ) ≤ ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 4
        ∂(Measure.pi fun _ : Fin n => F) := integral_nonneg fun y => by positivity
    have hM6n : (0 : ℝ) ≤ ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 6
        ∂(Measure.pi fun _ : Fin n => F) := integral_nonneg fun y => by positivity
    have hM8n : (0 : ℝ) ≤ ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 8
        ∂(Measure.pi fun _ : Fin n => F) := integral_nonneg fun y => by positivity
    have hM5 := abs_integral_odd_aux (Measure.pi fun _ : Fin n => F) hsumm hsumb
      two_mul_abs_pow_five_le
    have hM7 := abs_integral_odd_aux (Measure.pi fun _ : Fin n => F) hsumm hsumb
      two_mul_abs_pow_seven_le
    have hm0 : (∫ x, V x ^ 0 ∂F) = 1 := by simp
    have hm1 : (∫ x, V x ^ 1 ∂F) = 0 := by simpa using hV0
    have hM0 : (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 0
        ∂(Measure.pi fun _ : Fin n => F)) = 1 := by simp
    have hM1 : (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 1
        ∂(Measure.pi fun _ : Fin n => F)) = 0 := by simpa using h1
    have hstep := step_ten (n := n) (Bd := B) (a := ∫ x, V x ^ 2 ∂F)
      (b := ∫ x, V x ^ 4 ∂F) (m3 := ∫ x, V x ^ 3 ∂F) (m5 := ∫ x, V x ^ 5 ∂F)
      (m6 := ∫ x, V x ^ 6 ∂F) (m7 := ∫ x, V x ^ 7 ∂F) (m8 := ∫ x, V x ^ 8 ∂F)
      (m10 := ∫ x, V x ^ 10 ∂F)
      hB1 ha hb hM4 hM4n hM6 hM6n hM8 hM8n hM5 hM7 hm3' hm5' hm6' hm7' hm8' hm10' ih
    rw [integral_pi_sum_pow_succ F hV hB n 10]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose, hm0, hm1, hM0, hM1, hV0, h1, h2, h3]
    linarith [hstep]


/-- The same sandwich, for the *absolute* odd moment of the sum. -/
lemma integral_abs_pow_odd_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {S : α → ℝ} (hS : Measurable S) {D : ℝ} (hSb : ∀ z, |S z| ≤ D)
    {j i k : ℕ} (hpt : ∀ s : ℝ, 2 * |s ^ j| ≤ s ^ i + s ^ k) :
    ∫ z, |S z| ^ j ∂ν ≤ ((∫ z, S z ^ i ∂ν) + ∫ z, S z ^ k ∂ν) / 2 := by
  have hI1 : Integrable (fun z => |S z| ^ j) ν := by
    have h : (fun z => |S z| ^ j) = fun z => |S z ^ j| := by
      funext z; rw [abs_pow]
    rw [h]
    exact (integrable_pow_of_bounded ν hS hSb j).abs
  have hIi := integrable_pow_of_bounded ν hS hSb i
  have hIk := integrable_pow_of_bounded ν hS hSb k
  have hI2 : Integrable (fun z => (S z ^ i + S z ^ k) / 2) ν := (hIi.add hIk).div_const 2
  have h : ∫ z, |S z| ^ j ∂ν ≤ ∫ z, (S z ^ i + S z ^ k) / 2 ∂ν := by
    refine integral_mono hI1 hI2 fun z => ?_
    have := hpt (S z)
    rw [abs_pow] at this
    linarith
  have he : ∫ z, (S z ^ i + S z ^ k) / 2 ∂ν = ((∫ z, S z ^ i ∂ν) + ∫ z, S z ^ k ∂ν) / 2 := by
    rw [integral_div, integral_add hIi hIk]
  linarith [h, he]

/-- **The ninth absolute moment of the iid sum**, from orders eight and ten. -/
lemma integral_pi_sum_abs_pow_nine_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B)
    (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, |∑ i, V (y i)| ^ 9 ∂(Measure.pi fun _ : Fin n => F)
      ≤ 1200 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 4 * ((n : ℝ) ^ 4 + (n : ℝ) * B ^ 4)
        + 270000 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 5
            * ((n : ℝ) ^ 5 + (n : ℝ) * B ^ 6) := by
  have hsumm : Measurable fun z : Fin n → ℝ => ∑ i, V (z i) :=
    Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)
  have hsumb : ∀ z : Fin n → ℝ, |∑ i, V (z i)| ≤ (n : ℝ) * B := by
    intro z
    calc |∑ i, V (z i)| ≤ ∑ _i : Fin n, B :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB (z i))
      _ = (n : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := integral_abs_pow_odd_le (Measure.pi fun _ : Fin n => F) hsumm hsumb
    two_mul_abs_pow_nine_le
  have h8 := integral_pi_sum_pow_eight_le F hV hB hB1 hV0 n
  have h10 := integral_pi_sum_pow_ten_le F hV hB hB1 hV0 n
  linarith


/-! ### The WEIGHTED sandwich: the unweighted one is lossy at the second coordinate -/

lemma two_mul_abs_pow_five_weighted (t s : ℝ) : 2 * t * |s ^ 5| ≤ t ^ 2 * s ^ 4 + s ^ 6 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e4 : s ^ 4 = (|s| ^ 2) ^ 2 := by rw [h]; ring
  have e6 : s ^ 6 = (|s| ^ 2) ^ 3 := by rw [h]; ring
  rw [abs_pow, e4, e6]
  nlinarith [sq_nonneg (t * |s| ^ 2 - |s| ^ 3)]

lemma two_mul_abs_pow_seven_weighted (t s : ℝ) : 2 * t * |s ^ 7| ≤ t ^ 2 * s ^ 6 + s ^ 8 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e6 : s ^ 6 = (|s| ^ 2) ^ 3 := by rw [h]; ring
  have e8 : s ^ 8 = (|s| ^ 2) ^ 4 := by rw [h]; ring
  rw [abs_pow, e6, e8]
  nlinarith [sq_nonneg (t * |s| ^ 3 - |s| ^ 4)]

lemma two_mul_abs_pow_nine_weighted (t s : ℝ) : 2 * t * |s ^ 9| ≤ t ^ 2 * s ^ 8 + s ^ 10 := by
  have h : |s| ^ 2 = s ^ 2 := sq_abs s
  have e8 : s ^ 8 = (|s| ^ 2) ^ 4 := by rw [h]; ring
  have e10 : s ^ 10 = (|s| ^ 2) ^ 5 := by rw [h]; ring
  rw [abs_pow, e8, e10]
  nlinarith [sq_nonneg (t * |s| ^ 4 - |s| ^ 5)]

/-- The weighted sandwich under the integral. -/
lemma integral_abs_pow_odd_weighted {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {S : α → ℝ} (hS : Measurable S) {D : ℝ} (hSb : ∀ z, |S z| ≤ D)
    {j i k : ℕ} {t : ℝ} (ht : 0 < t)
    (hpt : ∀ s : ℝ, 2 * t * |s ^ j| ≤ t ^ 2 * s ^ i + s ^ k) :
    ∫ z, |S z| ^ j ∂ν ≤ (t * (∫ z, S z ^ i ∂ν) + (∫ z, S z ^ k ∂ν) / t) / 2 := by
  have hI1 : Integrable (fun z => |S z| ^ j) ν := by
    have h : (fun z => |S z| ^ j) = fun z => |S z ^ j| := by funext z; rw [abs_pow]
    rw [h]; exact (integrable_pow_of_bounded ν hS hSb j).abs
  have hIi := integrable_pow_of_bounded ν hS hSb i
  have hIk := integrable_pow_of_bounded ν hS hSb k
  have hI2 : Integrable (fun z => (t * S z ^ i + S z ^ k / t) / 2) ν :=
    ((hIi.const_mul t).add (hIk.div_const t)).div_const 2
  have h : ∫ z, |S z| ^ j ∂ν ≤ ∫ z, (t * S z ^ i + S z ^ k / t) / 2 ∂ν := by
    refine integral_mono hI1 hI2 fun z => ?_
    have hz := hpt (S z)
    rw [abs_pow] at hz
    have hkey : 2 * |S z| ^ j ≤ t * S z ^ i + S z ^ k / t := by
      have h2 : (2 * |S z| ^ j) * t ≤ (t * S z ^ i + S z ^ k / t) * t := by
        have e : (t * S z ^ i + S z ^ k / t) * t = t ^ 2 * S z ^ i + S z ^ k := by
          field_simp
        rw [e]; linarith [hz]
      exact le_of_mul_le_mul_right h2 ht
    linarith
  have he : ∫ z, (t * S z ^ i + S z ^ k / t) / 2 ∂ν
      = (t * (∫ z, S z ^ i ∂ν) + (∫ z, S z ^ k ∂ν) / t) / 2 := by
    rw [integral_div, integral_add (hIi.const_mul t) (hIk.div_const t),
      MeasureTheory.integral_const_mul, integral_div]
  linarith [h, he]


private lemma pi_sum_meas {V : ℝ → ℝ} (hV : Measurable V) (n : ℕ) :
    Measurable fun z : Fin n → ℝ => ∑ i, V (z i) :=
  Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)

private lemma pi_sum_bdd {V : ℝ → ℝ} {B : ℝ} (hB : ∀ x, |V x| ≤ B) (n : ℕ) :
    ∀ z : Fin n → ℝ, |∑ i, V (z i)| ≤ (n : ℝ) * B := by
  intro z
  calc |∑ i, V (z i)| ≤ ∑ _i : Fin n, B :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB (z i))
    _ = (n : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The fifth absolute moment of the iid sum**, weighted between orders four and six. -/
lemma integral_pi_sum_abs_pow_five_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B)
    (hV0 : ∫ x, V x ∂F = 0) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∫ y : Fin n → ℝ, |∑ i, V (y i)| ^ 5 ∂(Measure.pi fun _ : Fin n => F)
      ≤ (t * (3 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)))
          + (40 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 3
              * ((n : ℝ) ^ 3 + (n : ℝ) * B ^ 2)) / t) / 2 := by
  have h := integral_abs_pow_odd_weighted (Measure.pi fun _ : Fin n => F)
    (pi_sum_meas hV n) (pi_sum_bdd hB n) ht (two_mul_abs_pow_five_weighted t)
  have h4 := integral_pi_sum_pow_four_A F hV hB hV0 n
  have h6 := integral_pi_sum_pow_six_A F hV hB hB1 hV0 n
  have hd : ∀ x y : ℝ, x ≤ y → x / t ≤ y / t := fun x y hxy => by
    have h' := mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.2 ht))
    simpa [div_eq_mul_inv] using h'
  have := hd _ _ h6
  nlinarith [h, h4, this, ht]

/-- **The seventh absolute moment of the iid sum**, weighted between orders six and eight. -/
lemma integral_pi_sum_abs_pow_seven_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B)
    (hV0 : ∫ x, V x ∂F = 0) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∫ y : Fin n → ℝ, |∑ i, V (y i)| ^ 7 ∂(Measure.pi fun _ : Fin n => F)
      ≤ (t * (40 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 3
              * ((n : ℝ) ^ 3 + (n : ℝ) * B ^ 2))
          + (2400 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 4
              * ((n : ℝ) ^ 4 + (n : ℝ) * B ^ 4)) / t) / 2 := by
  have h := integral_abs_pow_odd_weighted (Measure.pi fun _ : Fin n => F)
    (pi_sum_meas hV n) (pi_sum_bdd hB n) ht (two_mul_abs_pow_seven_weighted t)
  have h6 := integral_pi_sum_pow_six_A F hV hB hB1 hV0 n
  have h8 := integral_pi_sum_pow_eight_le F hV hB hB1 hV0 n
  have hd : ∀ x y : ℝ, x ≤ y → x / t ≤ y / t := fun x y hxy => by
    have h' := mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.2 ht))
    simpa [div_eq_mul_inv] using h'
  have := hd _ _ h8
  nlinarith [h, h6, this, ht]

/-- **The ninth absolute moment of the iid sum**, weighted between orders eight and ten.  The
weight is essential: at the second coordinate of `Zₙ` the two neighbouring even moments are of
orders `n` and `n²`, so the *unweighted* sandwich returns `n²` where the graded ledger needs
`n^{3/2}`; the weight `t = √n` returns their geometric mean, which is `n^{3/2}` on the nose. -/
lemma integral_pi_sum_abs_pow_nine_weighted_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {V : ℝ → ℝ} (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hB1 : 1 ≤ B)
    (hV0 : ∫ x, V x ∂F = 0) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∫ y : Fin n → ℝ, |∑ i, V (y i)| ^ 9 ∂(Measure.pi fun _ : Fin n => F)
      ≤ (t * (2400 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 4
              * ((n : ℝ) ^ 4 + (n : ℝ) * B ^ 4))
          + (540000 * (1 + (∫ x, V x ^ 2 ∂F) + ∫ x, V x ^ 4 ∂F) ^ 5
              * ((n : ℝ) ^ 5 + (n : ℝ) * B ^ 6)) / t) / 2 := by
  have h := integral_abs_pow_odd_weighted (Measure.pi fun _ : Fin n => F)
    (pi_sum_meas hV n) (pi_sum_bdd hB n) ht (two_mul_abs_pow_nine_weighted t)
  have h8 := integral_pi_sum_pow_eight_le F hV hB hB1 hV0 n
  have h10 := integral_pi_sum_pow_ten_le F hV hB hB1 hV0 n
  have hd : ∀ x y : ℝ, x ≤ y → x / t ≤ y / t := fun x y hxy => by
    have h' := mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.2 ht))
    simpa [div_eq_mul_inv] using h'
  have := hd _ _ h10
  nlinarith [h, h8, this, ht]

end A51
