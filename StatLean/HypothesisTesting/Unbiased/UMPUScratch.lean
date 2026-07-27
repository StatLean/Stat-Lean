import StatLean.HypothesisTesting.Unbiased.MultiparamUMPU

/-! # Scratch: the secant separation for the point null -/

open MeasureTheory ProbabilityTheory

namespace StatLean.HypothesisTesting.Scratch3

/-- Three-point convexity of `u ↦ exp (c u)`, in cleared-denominator form. -/
lemma exp_three_point (c : ℝ) {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (z - x) * Real.exp (c * y)
      ≤ (z - y) * Real.exp (c * x) + (y - x) * Real.exp (c * z) := by
  have hzx : 0 < z - x := by linarith
  have hzxne : z - x ≠ 0 := ne_of_gt hzx
  set a : ℝ := (z - y) / (z - x) with ha
  set b : ℝ := (y - x) / (z - x) with hb
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hzx.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hzx.le
  have hab : a + b = 1 := by
    rw [ha, hb]; field_simp; ring
  have hmid : a * (c * x) + b * (c * z) = c * y := by
    rw [ha, hb]; field_simp; ring
  have hconv := convexOn_exp.2 (Set.mem_univ (c * x)) (Set.mem_univ (c * z)) ha0 hb0 hab
  simp only [smul_eq_mul] at hconv
  rw [hmid] at hconv
  have h := mul_le_mul_of_nonneg_left hconv hzx.le
  have hae : (z - x) * a = z - y := by rw [ha]; field_simp
  have hbe : (z - x) * b = y - x := by rw [hb]; field_simp
  have hrw : (z - x) * (a * Real.exp (c * x) + b * Real.exp (c * z))
      = (z - y) * Real.exp (c * x) + (y - x) * Real.exp (c * z) := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, hae, hbe]
  linarith [h, hrw.le, hrw.ge]

/-- **Secant separation.** For `C₁ < C₂` there is an affine function `A + B u` which meets
`exp (c u)` at `C₁` and `C₂`, lies above it strictly inside the interval and below it
outside. This is the separation that turns the multiplier form of the generalized
fundamental lemma into an *interval* rejection region for the point-null conditional test:
with `g = φ − ψ` one gets `g(u) · (exp (c u) − A − B u) ≥ 0` everywhere, and the two side
conditions (`∫ g = 0` and `∫ u g = 0`) kill the two affine terms. -/
lemma exists_sep_line (c : ℝ) {C₁ C₂ : ℝ} (hC : C₁ < C₂) :
    ∃ A B : ℝ,
      Real.exp (c * C₁) - A - B * C₁ = 0 ∧ Real.exp (c * C₂) - A - B * C₂ = 0 ∧
      (∀ u : ℝ, C₁ < u → u < C₂ → Real.exp (c * u) - A - B * u ≤ 0) ∧
      (∀ u : ℝ, u < C₁ ∨ C₂ < u → 0 ≤ Real.exp (c * u) - A - B * u) := by
  set E₁ : ℝ := Real.exp (c * C₁) with hE₁
  set E₂ : ℝ := Real.exp (c * C₂) with hE₂
  have hd : (0 : ℝ) < C₂ - C₁ := by linarith
  set B : ℝ := (E₂ - E₁) / (C₂ - C₁) with hB
  set A : ℝ := E₁ - B * C₁ with hA
  have hBd : B * (C₂ - C₁) = E₂ - E₁ := by
    rw [hB]; field_simp
  refine ⟨A, B, by rw [hA]; ring, ?_, ?_, ?_⟩
  · rw [hA]; linear_combination -hBd
  · intro u h1 h2
    have h3 := exp_three_point c h1 h2
    have hzero : (C₂ - u) * E₁ + (u - C₁) * E₂ - (C₂ - C₁) * (A + B * u) = 0 := by
      rw [hA]; linear_combination (C₁ - u) * hBd
    nlinarith [h3, hzero, hd]
  · intro u hu
    rcases hu with h | h
    · have h3 := exp_three_point c h hC
      have hzero : (C₂ - u) * E₁ + (u - C₁) * E₂ - (C₂ - C₁) * (A + B * u) = 0 := by
        rw [hA]; linear_combination (C₁ - u) * hBd
      nlinarith [h3, hzero, hd]
    · have h3 := exp_three_point c hC h
      have hzero : (C₂ - u) * E₁ + (u - C₁) * E₂ - (C₂ - C₁) * (A + B * u) = 0 := by
        rw [hA]; linear_combination (C₁ - u) * hBd
      nlinarith [h3, hzero, hd]

end StatLean.HypothesisTesting.Scratch3
