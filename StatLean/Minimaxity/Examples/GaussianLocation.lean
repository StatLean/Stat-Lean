import StatLean.Minimaxity.LeCam.TwoPoint
import StatLean.Minimaxity.ForMathlib.GaussianKL
import StatLean.Minimaxity.ForMathlib.PinskerInequality
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Example: Gaussian location family (Wainwright Examples 15.4, 15.10, 15.13)

The archetypal parametric minimax lower bound. For the Gaussian location family
`{𝒩(θ, σ²) : θ ∈ ℝ}` and `n` i.i.d. samples, the minimax risk for estimating the mean `θ` under
squared error scales as `σ²/n`:
```
inf_θ̂ sup_θ 𝔼_θ[(θ̂ − θ)²] ≥ σ²/(24 n)            (Example 15.4, Eq. (15.16b)).
```
This is obtained from Le Cam's two-point bound (`minimax_two_point`) with the Gaussian KL/TV bound;
the convex-hull (Example 15.10) and Fano (Example 15.13) routes give the same `σ²/n` order.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.4.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- **Crux: two-point total-variation bound for the Gaussian location family.** With the
separation `θ₁ = √(v/n)` the single-sample KL is `θ₁²/(2v) = 1/(2n)`, so the `n`-fold product KL
is `n·1/(2n) = 1/2`; Pinsker's inequality (Wainwright Lemma 15.2) then gives `‖·‖_TV ≤ √(KL/2) = 1/2`.
Uses `klDiv_gaussianReal` for the single-sample value and KL tensorization over the product. -/
private lemma gaussian_two_point_tvDist_le (n : ℕ) (hn : 1 ≤ n) (v : ℝ≥0) (hv : v ≠ 0)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => gaussianReal θ v) :
    tvDist (P 0) (P (Real.sqrt ((v : ℝ) / n))) ≤ 2⁻¹ := by
  set θ₁ : ℝ := Real.sqrt ((v : ℝ) / n) with hθ₁
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hvne : (v : ℝ) ≠ 0 := hv'.ne'
  -- the `n`-fold product KL equals `1/2`
  have hkl : klDiv (P θ₁) (P 0) = ENNReal.ofReal (1 / 2) := by
    rw [hP θ₁, hP 0, klDiv_pi_eq_nsmul, klDiv_gaussianReal _ _ _ hv, sub_zero, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hθsq : θ₁ ^ 2 = (v : ℝ) / n := Real.sq_sqrt (by positivity)
    rw [hθsq]
    field_simp
  -- Pinsker (reversed argument order): the KL on the RHS is `klDiv (P θ₁) (P 0)`
  calc tvDist (P 0) (P θ₁)
      ≤ (2⁻¹ * klDiv (P θ₁) (P 0)) ^ (1 / 2 : ℝ) := pinsker_tv_le_kl (P 0) (P θ₁)
    _ = 2⁻¹ := by
        rw [hkl,
            show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
              rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
                  ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by norm_num),
            show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num,
            ENNReal.ofReal_rpow_of_nonneg (by norm_num)
              (by norm_num : (0 : ℝ) ≤ 1 / 2),
            show ((1 / 4 : ℝ)) ^ (1 / 2 : ℝ) = 1 / 2 by
              rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
                  Real.sqrt_sq (by norm_num)],
            show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- **Minimax rate for the Gaussian location family** (Wainwright Example 15.4, Eq. (15.16b)): for
the `n`-sample model `P θ = 𝒩(θ, v)^{⊗n}`, the minimax risk for estimating the mean under squared
error is at least `v/(24n)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.4. -/
theorem gaussian_location_minimax_rate (n : ℕ) (hn : 1 ≤ n) (v : ℝ≥0) (hv : v ≠ 0)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    -- USER-INPUT: `P θ` is the `n`-fold i.i.d. `𝒩(θ, v)` product; Wainwright §15.2, Example 15.4.
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => gaussianReal θ v) :
    ENNReal.ofReal ((v : ℝ) / (24 * n)) ≤ minimaxRiskDist (· ^ 2) id P := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hθ₁0 : (0 : ℝ) ≤ Real.sqrt ((v : ℝ) / n) := Real.sqrt_nonneg _
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have hsep : 2 * ENNReal.ofReal (Real.sqrt ((v : ℝ) / n) / 2)
      ≤ edist (0 : ℝ) (Real.sqrt ((v : ℝ) / n)) := by
    rw [edist_dist, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hθ₁0,
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply le_of_eq; congr 1; ring
  have htv := gaussian_two_point_tvDist_le n hn v hv P hP
  have hΦδ : (fun x : ℝ≥0∞ => x ^ 2) (ENNReal.ofReal (Real.sqrt ((v : ℝ) / n) / 2))
      = ENNReal.ofReal ((v : ℝ) / (4 * n)) := by
    change (ENNReal.ofReal (Real.sqrt ((v : ℝ) / n) / 2)) ^ 2 = _
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [div_pow, Real.sq_sqrt (by positivity)]
    ring
  refine le_trans ?_ (minimax_two_point (fun x : ℝ≥0∞ => x ^ 2) id P 0
    (Real.sqrt ((v : ℝ) / n)) (ENNReal.ofReal (Real.sqrt ((v : ℝ) / n) / 2)) hΦ hsep)
  rw [hΦδ]
  have h2inv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  have hhalf : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ :=
    ENNReal.sub_eq_of_eq_add (by simp) ENNReal.inv_two_add_inv_two.symm
  have h1 : (2 : ℝ≥0∞)⁻¹ ≤ 1 - tvDist (P 0) (P (Real.sqrt ((v : ℝ) / n))) := by
    rw [← hhalf]; exact tsub_le_tsub_left htv 1
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hcompute : ENNReal.ofReal ((v : ℝ) / (4 * n)) / 2 * 2⁻¹
      = ENNReal.ofReal ((v : ℝ) / (16 * n)) := by
    rw [div_eq_mul_inv, h2inv, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((v : ℝ) / (24 * n))
      ≤ ENNReal.ofReal ((v : ℝ) / (16 * n)) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hv'.le
          (mul_pos (by norm_num) hn0) (by nlinarith [hn0.le]))
    _ = ENNReal.ofReal ((v : ℝ) / (4 * n)) / 2 * 2⁻¹ := hcompute.symm
    _ ≤ ENNReal.ofReal ((v : ℝ) / (4 * n)) / 2
          * (1 - tvDist (P 0) (P (Real.sqrt ((v : ℝ) / n)))) := mul_le_mul' le_rfl h1

end StatLean.Minimaxity
