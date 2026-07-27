import StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-- To bound a square root it is enough to bound the radicand by a square. -/
private lemma sqrt_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (hxy : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hxy
    _ = y := Real.sqrt_sq hy

/-- **Cauchy–Schwarz for a finite average**: the average of `|f|` is at most the square root
of the average of `f²`. -/
private lemma avg_abs_le_sqrt_avg_sq {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|
      ≤ Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2) := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i| :=
    mul_nonneg (inv_nonneg.2 hc.le) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hcs : (∑ i, |f i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => |f i|)
    simpa [Finset.card_univ, sq_abs] using h
  calc (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|
      = Real.sqrt (((Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow]
        have hstep : ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ i, |f i|) ^ 2
            ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
        calc ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ i, |f i|) ^ 2
            ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) := hstep
          _ = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2 := by field_simp

/-- The elementary cube inequality `|x − y|³ ≤ 4(|x|³ + |y|³)`. -/
private lemma abs_sub_cube_le (x y : ℝ) : |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have h1 : |x - y| ≤ |x| + |y| := by
    have h := abs_add_le x (-y)
    simpa [sub_eq_add_neg, abs_neg] using h
  have h2 : |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg _) h1 3
  nlinarith [abs_nonneg x, abs_nonneg y,
    mul_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y)) (sq_nonneg (|x| - |y|))]

/-- `xy/(x+y) ≤ min x y`: the Stein scale is at most Hájek's scale. -/
private lemma mul_div_add_le_min {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * y / (x + y) ≤ min x y := by
  have hxy : (0 : ℝ) < x + y := by linarith
  refine le_min ?_ ?_
  · rw [div_le_iff₀ hxy]; nlinarith
  · rw [div_le_iff₀ hxy]; nlinarith

/-- `min x y ≤ 2 xy/(x+y)`: Hájek's scale is at most twice the Stein scale. -/
private lemma min_div_two_le_mul_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    min x y / 2 ≤ x * y / (x + y) := by
  have hxy : (0 : ℝ) < x + y := by linarith
  rw [div_le_div_iff₀ (by norm_num) hxy]
  rcases le_total x y with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

end StatLean.HypothesisTesting
