import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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

end A51
