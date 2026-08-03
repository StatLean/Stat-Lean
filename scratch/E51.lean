import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

open MeasureTheory

namespace E51

noncomputable def surrogateRemGraded (θ u v r : ℝ) : ℝ :=
  |θ| ^ 3 * (r * (|u| * |v| / 2) + r ^ 2 * (|u| ^ 3 / 2 + 3 * |u| * |v| ^ 2 / 8)) ^ 3 / 6
    + θ ^ 2 / 2 * (r ^ 3 * (|u| * |v| * (|u| ^ 3 / 2 + 3 * |u| * |v| ^ 2 / 8))
        + r ^ 4 * (|u| ^ 3 / 2 + 3 * |u| * |v| ^ 2 / 8) ^ 2)

noncomputable def surrGradedLin (σ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |w 0 / σ| * |w 1 / σ ^ 2| / 2

noncomputable def surrGradedBlk (σ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |w 0 / σ| ^ 3 / 2 + 3 * |w 0 / σ| * |w 1 / σ ^ 2| ^ 2 / 8

lemma surrGradedLin_nonneg (σ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : 0 ≤ surrGradedLin σ w := by
  rw [surrGradedLin]; positivity

lemma surrGradedBlk_nonneg (σ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : 0 ≤ surrGradedBlk σ w := by
  rw [surrGradedBlk]; positivity

theorem integral_surrogateRemGraded_le_of_graded (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {σ r : ℝ} (hr : 0 ≤ r) (θ : ℝ) {N₃ N₄ N₅ N₆ Q₃ Q₄ : ℝ}
    (hi₃ : Integrable (fun w => surrGradedLin σ w ^ 3) μ)
    (hi₄ : Integrable (fun w => surrGradedLin σ w ^ 2 * surrGradedBlk σ w) μ)
    (hi₅ : Integrable (fun w => surrGradedLin σ w * surrGradedBlk σ w ^ 2) μ)
    (hi₆ : Integrable (fun w => surrGradedBlk σ w ^ 3) μ)
    (hq₃ : Integrable (fun w => surrGradedLin σ w * surrGradedBlk σ w) μ)
    (hq₄ : Integrable (fun w => surrGradedBlk σ w ^ 2) μ)
    (h₃ : (∫ w, surrGradedLin σ w ^ 3 ∂μ) ≤ N₃)
    (h₄ : (∫ w, surrGradedLin σ w ^ 2 * surrGradedBlk σ w ∂μ) ≤ N₄)
    (h₅ : (∫ w, surrGradedLin σ w * surrGradedBlk σ w ^ 2 ∂μ) ≤ N₅)
    (h₆ : (∫ w, surrGradedBlk σ w ^ 3 ∂μ) ≤ N₆)
    (hQ₃ : (∫ w, surrGradedLin σ w * surrGradedBlk σ w ∂μ) ≤ Q₃)
    (hQ₄ : (∫ w, surrGradedBlk σ w ^ 2 ∂μ) ≤ Q₄) :
    ∫ w, surrogateRemGraded θ (w 0 / σ) (w 1 / σ ^ 2) r ∂μ
      ≤ r ^ 3 * (|θ| ^ 3 / 6 * (N₃ + 3 * r * N₄ + 3 * r ^ 2 * N₅ + r ^ 3 * N₆)
          + θ ^ 2 / 2 * (2 * Q₃ + r * Q₄)) := sorry

lemma max_pow_le_add {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (d : ℕ) :
    (max X Y) ^ d ≤ X ^ d + Y ^ d := by
  rcases le_total X Y with h | h
  · rw [max_eq_right h]
    have : (0 : ℝ) ≤ X ^ d := pow_nonneg hX d
    linarith
  · rw [max_eq_left h]
    have : (0 : ℝ) ≤ Y ^ d := pow_nonneg hY d
    linarith

/-- `P = XY/2 ≤ M²/2` and `A = X³/2 + 3XY²/8 ≤ (7/8)M³` at `M = max X Y`. -/
lemma blocks_le_max {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    X * Y / 2 ≤ (max X Y) ^ 2 / 2 ∧
      X ^ 3 / 2 + 3 * X * Y ^ 2 / 8 ≤ 7 / 8 * (max X Y) ^ 3 := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max X Y := ⟨_, rfl⟩
  rw [← hMdef]
  have hXM : X ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hYM : Y ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM0 : 0 ≤ M := le_trans hX hXM
  have h2 : X * Y ≤ M ^ 2 := by nlinarith
  have h3 : X ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ hX hXM 3
  have hy2 : Y ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hY hYM 2
  have h3' : X * Y ^ 2 ≤ M ^ 3 := by nlinarith [pow_nonneg hY 2, pow_nonneg hM0 2]
  constructor
  · linarith
  · linarith

/-- Each of the six graded blocks is a constant times a power of `M = max X Y`. -/
lemma six_blocks_le_max {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (X * Y / 2) ^ 3 ≤ 1 / 8 * (max X Y) ^ 6 ∧
    (X * Y / 2) ^ 2 * (X ^ 3 / 2 + 3 * X * Y ^ 2 / 8) ≤ 7 / 32 * (max X Y) ^ 7 ∧
    (X * Y / 2) * (X ^ 3 / 2 + 3 * X * Y ^ 2 / 8) ^ 2 ≤ 49 / 128 * (max X Y) ^ 8 ∧
    (X ^ 3 / 2 + 3 * X * Y ^ 2 / 8) ^ 3 ≤ 343 / 512 * (max X Y) ^ 9 ∧
    (X * Y / 2) * (X ^ 3 / 2 + 3 * X * Y ^ 2 / 8) ≤ 7 / 16 * (max X Y) ^ 5 ∧
    (X ^ 3 / 2 + 3 * X * Y ^ 2 / 8) ^ 2 ≤ 49 / 64 * (max X Y) ^ 6 := by
  obtain ⟨hP, hA⟩ := blocks_le_max hX hY
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max X Y := ⟨_, rfl⟩
  rw [← hMdef] at hP hA ⊢
  have hM0 : 0 ≤ M := le_trans hX (by rw [hMdef]; exact le_max_left _ _)
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = X * Y / 2 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = X ^ 3 / 2 + 3 * X * Y ^ 2 / 8 := ⟨_, rfl⟩
  rw [← hPdef] at hP
  rw [← hAdef] at hA
  rw [← hPdef, ← hAdef]
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hM2 : (0 : ℝ) ≤ M ^ 2 := by positivity
  have hM3 : (0 : ℝ) ≤ M ^ 3 := by positivity
  have hP2 : P ^ 2 ≤ (M ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hP0 hP 2
  have hP3 : P ^ 3 ≤ (M ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hP0 hP 3
  have hA2 : A ^ 2 ≤ (7 / 8 * M ^ 3) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have hA3 : A ^ 3 ≤ (7 / 8 * M ^ 3) ^ 3 := pow_le_pow_left₀ hA0 hA 3
  refine ⟨by nlinarith [hP3], ?_, ?_, by nlinarith [hA3], ?_, by nlinarith [hA2]⟩
  · have h : P ^ 2 * A ≤ (M ^ 2 / 2) ^ 2 * (7 / 8 * M ^ 3) :=
      mul_le_mul hP2 hA hA0 (by positivity)
    nlinarith [h]
  · have h : P * A ^ 2 ≤ (M ^ 2 / 2) * ((7 / 8 * M ^ 3) ^ 2) :=
      mul_le_mul hP hA2 (by positivity) (by positivity)
    nlinarith [h]
  · have h : P * A ≤ (M ^ 2 / 2) * (7 / 8 * M ^ 3) := mul_le_mul hP hA hA0 (by positivity)
    nlinarith [h]


/-! ### The six blocks against the scalar absolute moments of the two coordinates -/

private lemma measurable_surrGradedLin (σ : ℝ) : Measurable (surrGradedLin σ) := by
  unfold surrGradedLin; fun_prop

private lemma measurable_surrGradedBlk (σ : ℝ) : Measurable (surrGradedBlk σ) := by
  unfold surrGradedBlk; fun_prop

lemma surrGraded_six_blocks_le (σ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    surrGradedLin σ w ^ 3 ≤ 1 / 8 * (|w 0 / σ| ^ 6 + |w 1 / σ ^ 2| ^ 6) ∧
    surrGradedLin σ w ^ 2 * surrGradedBlk σ w
      ≤ 7 / 32 * (|w 0 / σ| ^ 7 + |w 1 / σ ^ 2| ^ 7) ∧
    surrGradedLin σ w * surrGradedBlk σ w ^ 2
      ≤ 49 / 128 * (|w 0 / σ| ^ 8 + |w 1 / σ ^ 2| ^ 8) ∧
    surrGradedBlk σ w ^ 3 ≤ 343 / 512 * (|w 0 / σ| ^ 9 + |w 1 / σ ^ 2| ^ 9) ∧
    surrGradedLin σ w * surrGradedBlk σ w
      ≤ 7 / 16 * (|w 0 / σ| ^ 5 + |w 1 / σ ^ 2| ^ 5) ∧
    surrGradedBlk σ w ^ 2 ≤ 49 / 64 * (|w 0 / σ| ^ 6 + |w 1 / σ ^ 2| ^ 6) := by
  have hX : (0 : ℝ) ≤ |w 0 / σ| := abs_nonneg _
  have hY : (0 : ℝ) ≤ |w 1 / σ ^ 2| := abs_nonneg _
  obtain ⟨b3, b4, b5, b6, q3, q4⟩ := six_blocks_le_max hX hY
  have m5 := max_pow_le_add hX hY 5
  have m6 := max_pow_le_add hX hY 6
  have m7 := max_pow_le_add hX hY 7
  have m8 := max_pow_le_add hX hY 8
  have m9 := max_pow_le_add hX hY 9
  rw [surrGradedLin, surrGradedBlk]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The pattern each block runs through: a pointwise domination by `c(Xᵈ + Yᵈ)` gives both
integrability and the integral bound. -/
private lemma block_integrable_and_le (μ : Measure (EuclideanSpace ℝ (Fin 2))) {σ : ℝ}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hfm : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    {c : ℝ} (hc : 0 ≤ c) {d : ℕ} {Sd : ℝ}
    (hle : ∀ w, f w ≤ c * (|w 0 / σ| ^ d + |w 1 / σ ^ 2| ^ d))
    (hia : Integrable (fun w : EuclideanSpace ℝ (Fin 2) => |w 0 / σ| ^ d) μ)
    (hib : Integrable (fun w : EuclideanSpace ℝ (Fin 2) => |w 1 / σ ^ 2| ^ d) μ)
    (hSd : (∫ w, |w 0 / σ| ^ d ∂μ) + ∫ w, |w 1 / σ ^ 2| ^ d ∂μ ≤ Sd) :
    Integrable f μ ∧ (∫ w, f w ∂μ) ≤ c * Sd := by
  have maj : Integrable
      (fun w : EuclideanSpace ℝ (Fin 2) => c * (|w 0 / σ| ^ d + |w 1 / σ ^ 2| ^ d)) μ :=
    (hia.add hib).const_mul c
  have hI : Integrable f μ := by
    refine Integrable.mono' maj hfm.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]
    exact hle w
  refine ⟨hI, ?_⟩
  have h1 : (∫ w, f w ∂μ)
      ≤ ∫ w, c * (|w 0 / σ| ^ d + |w 1 / σ ^ 2| ^ d) ∂μ := integral_mono hI maj hle
  have h2 : (∫ w : EuclideanSpace ℝ (Fin 2), c * (|w 0 / σ| ^ d + |w 1 / σ ^ 2| ^ d) ∂μ)
      = c * ((∫ w, |w 0 / σ| ^ d ∂μ) + ∫ w, |w 1 / σ ^ 2| ^ d ∂μ) := by
    rw [MeasureTheory.integral_const_mul, integral_add hia hib]
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hSd hc)

/-- **`hRg` AT `Zₙ`, IN FIVE SCALAR ABSOLUTE MOMENTS, WITH THE GRADING KEPT.** -/
theorem integral_surrogateRemGraded_le_of_scalar_moments
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {σ r : ℝ} (hr : 0 ≤ r) (θ : ℝ) {S : ℕ → ℝ}
    (hia : ∀ d : ℕ, Integrable (fun w : EuclideanSpace ℝ (Fin 2) => |w 0 / σ| ^ d) μ)
    (hib : ∀ d : ℕ, Integrable (fun w : EuclideanSpace ℝ (Fin 2) => |w 1 / σ ^ 2| ^ d) μ)
    (hS : ∀ d : ℕ, (∫ w, |w 0 / σ| ^ d ∂μ) + ∫ w, |w 1 / σ ^ 2| ^ d ∂μ ≤ S d) :
    ∫ w, surrogateRemGraded θ (w 0 / σ) (w 1 / σ ^ 2) r ∂μ
      ≤ r ^ 3 * (|θ| ^ 3 / 6 * (1 / 8 * S 6 + 3 * r * (7 / 32 * S 7)
            + 3 * r ^ 2 * (49 / 128 * S 8) + r ^ 3 * (343 / 512 * S 9))
          + θ ^ 2 / 2 * (2 * (7 / 16 * S 5) + r * (49 / 64 * S 6))) := by
  have hmL := measurable_surrGradedLin σ
  have hmB := measurable_surrGradedBlk σ
  have hL0 := surrGradedLin_nonneg σ
  have hB0 := surrGradedBlk_nonneg σ
  obtain ⟨i₃, h₃⟩ := block_integrable_and_le μ (hmL.pow_const 3)
    (fun w => pow_nonneg (hL0 w) 3) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (fun w => (surrGraded_six_blocks_le σ w).1) (hia 6) (hib 6) (hS 6)
  obtain ⟨i₄, h₄⟩ := block_integrable_and_le μ ((hmL.pow_const 2).mul hmB)
    (fun w => mul_nonneg (pow_nonneg (hL0 w) 2) (hB0 w)) (by norm_num : (0 : ℝ) ≤ 7 / 32)
    (fun w => (surrGraded_six_blocks_le σ w).2.1) (hia 7) (hib 7) (hS 7)
  obtain ⟨i₅, h₅⟩ := block_integrable_and_le μ (hmL.mul (hmB.pow_const 2))
    (fun w => mul_nonneg (hL0 w) (pow_nonneg (hB0 w) 2)) (by norm_num : (0 : ℝ) ≤ 49 / 128)
    (fun w => (surrGraded_six_blocks_le σ w).2.2.1) (hia 8) (hib 8) (hS 8)
  obtain ⟨i₆, h₆⟩ := block_integrable_and_le μ (hmB.pow_const 3)
    (fun w => pow_nonneg (hB0 w) 3) (by norm_num : (0 : ℝ) ≤ 343 / 512)
    (fun w => (surrGraded_six_blocks_le σ w).2.2.2.1) (hia 9) (hib 9) (hS 9)
  obtain ⟨iq₃, hq₃⟩ := block_integrable_and_le μ (hmL.mul hmB)
    (fun w => mul_nonneg (hL0 w) (hB0 w)) (by norm_num : (0 : ℝ) ≤ 7 / 16)
    (fun w => (surrGraded_six_blocks_le σ w).2.2.2.2.1) (hia 5) (hib 5) (hS 5)
  obtain ⟨iq₄, hq₄⟩ := block_integrable_and_le μ (hmB.pow_const 2)
    (fun w => pow_nonneg (hB0 w) 2) (by norm_num : (0 : ℝ) ≤ 49 / 64)
    (fun w => (surrGraded_six_blocks_le σ w).2.2.2.2.2) (hia 6) (hib 6) (hS 6)
  exact integral_surrogateRemGraded_le_of_graded μ hr θ i₃ i₄ i₅ i₆ iq₃ iq₄
    h₃ h₄ h₅ h₆ hq₃ hq₄

end E51
