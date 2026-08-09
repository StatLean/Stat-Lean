import StatLean.StatisticalLearning.Rademacher.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators

namespace StatLean.StatisticalLearning

variable {n : ℕ}

/-! ### The sign-average toolkit -/

/-- Global sign flip as an involutive equivalence of sign patterns. -/
def flipSigns (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ i := !σ i
  invFun σ i := !σ i
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

lemma signOf_flipSigns (σ : Fin n → Bool) : signOf (flipSigns n σ) = -signOf σ := by
  funext i
  simp only [signOf, flipSigns, Equiv.coe_fn_mk, Pi.neg_apply]
  by_cases h : σ i = true <;> simp [h]

lemma signAvg_comp_neg (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => g (-ε)) = signAvg n g := by
  unfold signAvg
  congr 1
  refine Fintype.sum_equiv (flipSigns n) _ _ fun σ => ?_
  rw [signOf_flipSigns]

lemma signAvg_comp_neg' (n : ℕ) (F G : (Fin n → ℝ) → ℝ) (h : ∀ ε, F ε = G (-ε)) :
    signAvg n F = signAvg n G := by
  rw [show F = fun ε => G (-ε) from funext h]
  exact signAvg_comp_neg n G

lemma signAvg_add (n : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => f ε + g ε) = signAvg n f + signAvg n g := by
  unfold signAvg
  rw [Finset.sum_add_distrib]
  ring

lemma signAvg_const_mul (n : ℕ) (c : ℝ) (g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => c * g ε) = c * signAvg n g := by
  unfold signAvg
  rw [← Finset.mul_sum]
  ring

lemma signAvg_mono (n : ℕ) {f g : (Fin n → ℝ) → ℝ} (h : ∀ ε, f ε ≤ g ε) :
    signAvg n f ≤ signAvg n g := by
  unfold signAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h _) (by positivity)

lemma signAvg_sum {ι : Type*} (n : ℕ) (s : Finset ι) (g : ι → (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => ∑ a ∈ s, g a ε) = ∑ a ∈ s, signAvg n (g a) := by
  simp only [signAvg, ← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

lemma signAvg_odd (n : ℕ) {g : (Fin n → ℝ) → ℝ} (h : ∀ ε, g (-ε) = -g ε) :
    signAvg n g = 0 := by
  have h1 : signAvg n (fun ε => g (-ε)) = signAvg n g := signAvg_comp_neg n g
  have h2 : signAvg n (fun ε => g (-ε)) = signAvg n (fun ε => (-1 : ℝ) * g ε) := by
    congr 1
    funext ε
    rw [h ε]
    ring
  rw [h2, signAvg_const_mul] at h1
  linarith

lemma signAvg_inner_eq_zero (n : ℕ) (a₀ : Fin n → ℝ) :
    signAvg n (fun ε => ∑ i, ε i * a₀ i) = 0 := by
  refine signAvg_odd n fun ε => ?_
  simp [Finset.sum_neg_distrib]

lemma image_inner_neg (A : Set (Fin n → ℝ)) (ε : Fin n → ℝ) :
    (fun a => ∑ i, ε i * a i) '' ((fun a => -a) '' A)
      = (fun a => ∑ i, (-ε) i * a i) '' A := by
  rw [Set.image_image]
  congr 1
  funext a
  simp

/-! ### Structural lemmas -/

theorem radComplexity_neg' (A : Set (Fin n → ℝ)) :
    radComplexity ((fun a => -a) '' A) = radComplexity A := by
  unfold radComplexity
  congr 1
  refine signAvg_comp_neg' n _ _ fun ε => ?_
  rw [image_inner_neg]

theorem radComplexity_translate' (A : Set (Fin n → ℝ)) (a₀ : Fin n → ℝ)
    (hne : A.Nonempty)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => a + a₀) '' A) = radComplexity A := by
  unfold radComplexity
  congr 1
  have key : (fun ε : Fin n → ℝ =>
        sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => a + a₀) '' A)))
      = fun ε : Fin n → ℝ =>
        sSup ((fun a => ∑ i, ε i * a i) '' A) + ∑ i, ε i * a₀ i := by
    funext ε
    have himg : (fun a => ∑ i, ε i * a i) '' ((fun a : Fin n → ℝ => a + a₀) '' A)
        = (fun t : ℝ => t + ∑ i, ε i * a₀ i) '' ((fun a => ∑ i, ε i * a i) '' A) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext a
      simp [mul_add, Finset.sum_add_distrib]
    rw [himg]
    have := (OrderIso.addRight (∑ i, ε i * a₀ i)).map_csSup'
      (hne.image (fun a => ∑ i, ε i * a i)) (hbdd ε)
    simpa using this.symm
  rw [key, signAvg_add, signAvg_inner_eq_zero, add_zero]

theorem radComplexity_smul_le_of_nonneg (A : Set (Fin n → ℝ)) {c : ℝ} (hc : 0 ≤ c)
    (hne : A.Nonempty)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => c • a) '' A) ≤ c * radComplexity A := by
  have hstep : ∀ ε : Fin n → ℝ,
      sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => c • a) '' A))
        ≤ c * sSup ((fun a => ∑ i, ε i * a i) '' A) := by
    intro ε
    have himg : (fun a => ∑ i, ε i * a i) '' ((fun a : Fin n → ℝ => c • a) '' A)
        = (fun t : ℝ => c * t) '' ((fun a => ∑ i, ε i * a i) '' A) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]; ring
    rw [himg]
    refine csSup_le ((hne.image _).image _) ?_
    rintro x ⟨t, ht, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup (hbdd ε) ht) hc
  unfold radComplexity
  have h1 : signAvg n
        (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => c • a) '' A)))
      ≤ c * signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A)) := by
    rw [← signAvg_const_mul]
    exact signAvg_mono n hstep
  calc (n : ℝ)⁻¹ * signAvg n
        (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => c • a) '' A)))
      ≤ (n : ℝ)⁻¹ * (c * signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c * ((n : ℝ)⁻¹ * signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A))) := by
        ring

theorem radComplexity_smul_le' (A : Set (Fin n → ℝ)) (c : ℝ) (hne : A.Nonempty)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => c • a) '' A) ≤ |c| * radComplexity A := by
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    exact radComplexity_smul_le_of_nonneg A hc hne hbdd
  · have hA' : ((fun a : Fin n → ℝ => c • a) '' A)
        = (fun a : Fin n → ℝ => |c| • a) '' ((fun a => -a) '' A) := by
      rw [Set.image_image]
      congr 1
      funext a
      funext i
      simp [abs_of_neg hc]
    rw [hA']
    have hne' : ((fun a : Fin n → ℝ => -a) '' A).Nonempty := hne.image _
    have hbdd' : ∀ ε : Fin n → ℝ,
        BddAbove ((fun a => ∑ i, ε i * a i) '' ((fun a : Fin n → ℝ => -a) '' A)) := by
      intro ε
      rw [image_inner_neg]
      exact hbdd (-ε)
    calc radComplexity ((fun a : Fin n → ℝ => |c| • a) '' ((fun a => -a) '' A))
        ≤ |c| * radComplexity ((fun a : Fin n → ℝ => -a) '' A) :=
          radComplexity_smul_le_of_nonneg _ (abs_nonneg c) hne' hbdd'
      _ = |c| * radComplexity A := by rw [radComplexity_neg']

theorem add_exp_neg_div_two_le_exp_sq' (a : ℝ) :
    (Real.exp a + Real.exp (-a)) / 2 ≤ Real.exp (a ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq a
  rwa [Real.cosh_eq] at h

end StatLean.StatisticalLearning
