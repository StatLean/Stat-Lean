import StatLean.HypothesisTesting.GoodnessOfFit.SmoothTest
import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity

/-! Scratch development file for wave-5 lane B.  Not part of the library. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators NNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-- local copy of the private `psiVec` of `SmoothTest.lean`. -/
private noncomputable def psiVec' {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (x : 𝓧) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ψ j x)

private lemma inner_eucl_sum' {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma inner_psiVec' {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : 𝓧) : ⟪u, psiVec' ψ x⟫_ℝ = ∑ j, u j * ψ j x := by
  rw [inner_eucl_sum']
  exact Finset.sum_congr rfl fun j _ => rfl

/-! ### Elementary real inequalities -/

/-- `|e^z − (1 + z + z²/2)| ≤ 4 |z|³ e^{|z|}` for every real `z`. -/
private lemma abs_exp_sub_quadratic_le (z : ℝ) :
    |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ 4 * |z| ^ 3 * Real.exp |z| := by
  have hexp1 : (1 : ℝ) ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  have hcube0 : (0 : ℝ) ≤ |z| ^ 3 := pow_nonneg (abs_nonneg z) 3
  rcases le_or_gt |z| 1 with hle | hgt
  · have h := Real.exp_bound hle (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, z ^ m / (Nat.factorial m) = 1 + z + z ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    have hcoef : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 4 := by
      norm_num [Nat.factorial]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |z| ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3) * 3)) := h
      _ ≤ |z| ^ 3 * 4 := by nlinarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith
  · -- `|z| > 1`: crude triangle-inequality bound
    have habs0 : (0 : ℝ) ≤ |z| := abs_nonneg z
    have h1 : (1 : ℝ) ≤ |z| ^ 3 := one_le_pow₀ hgt.le
    have hd : 0 ≤ |z| * ((|z| - 1) * (|z| + 1)) :=
      mul_nonneg habs0 (mul_nonneg (by linarith) (by linarith))
    have hz : |z| ≤ |z| ^ 3 := by nlinarith
    have hd2 : 0 ≤ (|z| * |z|) * (|z| - 1) :=
      mul_nonneg (mul_nonneg habs0 habs0) (by linarith)
    have hz2 : z ^ 2 ≤ |z| ^ 3 := by
      have hsq : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      nlinarith
    have hexpz : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
    have htri : |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_neg]
    have hterm : |1 + z + z ^ 2 / 2| ≤ 3 * |z| ^ 3 := by
      have hb : |1 + z + z ^ 2 / 2| ≤ 1 + |z| + z ^ 2 / 2 := by
        have h₁ : |1 + z + z ^ 2 / 2| ≤ |1 + z| + |z ^ 2 / 2| := abs_add_le _ _
        have h₂ : |1 + z| ≤ 1 + |z| := by
          calc |1 + z| ≤ |(1 : ℝ)| + |z| := abs_add_le _ _
            _ = 1 + |z| := by norm_num
        have h₃ : |z ^ 2 / 2| = z ^ 2 / 2 := abs_of_nonneg (by positivity)
        linarith
      linarith
    have hexpabs : |Real.exp z| = Real.exp z := abs_of_nonneg (Real.exp_pos z).le
    have hstep : Real.exp |z| ≤ |z| ^ 3 * Real.exp |z| := by nlinarith [Real.exp_pos |z|]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := htri
      _ ≤ Real.exp |z| + 3 * |z| ^ 3 := by rw [hexpabs]; linarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith

/-- `|log (1 + w) − w| ≤ w²` for `w ≥ 0`. -/
private lemma abs_log_one_add_sub_le (w : ℝ) (hw : 0 ≤ w) :
    |Real.log (1 + w) - w| ≤ w ^ 2 := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  have hup : Real.log (1 + w) ≤ w := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : w - w ^ 2 ≤ Real.log (1 + w) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + w)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hne : (1 : ℝ) + w ≠ 0 := ne_of_gt hpos
    have hkey : 1 - (1 + w)⁻¹ = w / (1 + w) := by field_simp; ring
    have h3 : w - w ^ 2 ≤ 1 - (1 + w)⁻¹ := by
      rw [hkey, le_div_iff₀ hpos]
      nlinarith [pow_nonneg hw 3]
    linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `u³ ≤ 6 t⁻³ e^{t u}` for `u ≥ 0`, `t > 0`. -/
private lemma cube_le_exp (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 6 / t ^ 3 * Real.exp (t * u) := by
  have h := Real.sum_le_exp_of_nonneg (x := t * u) (by positivity) 4
  have hsum : ∑ m ∈ Finset.range 4, (t * u) ^ m / (Nat.factorial m)
      = 1 + t * u + (t * u) ^ 2 / 2 + (t * u) ^ 3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have htu : 0 ≤ t * u := by positivity
  have hcube : (t * u) ^ 3 / 6 ≤ Real.exp (t * u) := by nlinarith [sq_nonneg (t * u)]
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ht3]
  nlinarith

end StatLean.HypothesisTesting
