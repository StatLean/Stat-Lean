import StatLean.Minimaxity.LeCam.TwoPoint
import StatLean.Minimaxity.ForMathlib.LeCamInequality

/-!
# Example: uniform location family (Wainwright Example 15.5)

A non-regular parametric problem with a faster-than-`1/n` rate. For the uniform location family
`{Uniform[θ, θ+1] : θ ∈ ℝ}` and `n` i.i.d. samples, the Kullback–Leibler divergence is infinite for
distinct parameters, so Le Cam's two-point bound is applied via the **Hellinger** distance (Lemma
15.3) instead of Pinsker. The resulting minimax risk scales as `n⁻²`:
```
inf_θ̂ sup_θ 𝔼_θ[(θ̂ − θ)²] ≥ (1 − 1/√2)/128 · 1/n²        (Example 15.5).
```

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Crux: two-point total-variation bound for the uniform location family.** With the separation
`θ₁ = 1/n`, Le Cam's inequality (Wainwright Lemma 15.3, `lecam_tv_le_hellinger`) applied to the
`n`-fold product, together with the squared-Hellinger computation for the unit-interval shift,
yields `1 − ‖·‖_TV ≥ (1 − 1/√2)/16`. -/
private lemma uniform_two_point_tvDist_bound (n : ℕ) (hn : 1 ≤ n)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc θ (θ + 1))) :
    ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16) ≤ 1 - tvDist (P 0) (P ((n : ℝ)⁻¹)) := by
  sorry -- TODO(mmx): n-fold Le Cam/Hellinger (15.3) + squared-Hellinger of the unit-interval shift

/-- **Minimax rate for the uniform location family** (Wainwright Example 15.5): for the `n`-sample
model `P θ = Uniform[θ, θ+1]^{⊗n}`, the minimax risk for estimating `θ` under squared error is at
least `(1 − 1/√2)/128 · n⁻²` — the faster `n⁻²` rate of a non-regular problem.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.5. -/
theorem uniform_location_minimax_rate (n : ℕ) (hn : 1 ≤ n)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    -- USER-INPUT: `P θ` is the `n`-fold i.i.d. `Uniform[θ, θ+1]` product; Wainwright §15.2, Ex 15.5.
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc θ (θ + 1))) :
    ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2)
      ≤ minimaxRiskDist (· ^ 2) id P := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hB : (0 : ℝ) ≤ (1 - 1 / Real.sqrt 2) / 16 := by
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have : 1 / Real.sqrt 2 ≤ 1 := (div_le_one h2pos).mpr hsqrt2
    linarith
  have hθ₁0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have hsep : 2 * ENNReal.ofReal ((n : ℝ)⁻¹ / 2) ≤ edist (0 : ℝ) ((n : ℝ)⁻¹) := by
    rw [edist_dist, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hθ₁0,
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply le_of_eq; congr 1; ring
  have hcrux := uniform_two_point_tvDist_bound n hn P hP
  have hΦδ : (fun x : ℝ≥0∞ => x ^ 2) (ENNReal.ofReal ((n : ℝ)⁻¹ / 2))
      = ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) := by
    change (ENNReal.ofReal ((n : ℝ)⁻¹ / 2)) ^ 2 = _
    rw [← ENNReal.ofReal_pow (by positivity)]
  refine le_trans ?_ (minimax_two_point (fun x : ℝ≥0∞ => x ^ 2) id P 0
    ((n : ℝ)⁻¹) (ENNReal.ofReal ((n : ℝ)⁻¹ / 2)) hΦ hsep)
  rw [hΦδ]
  have h2inv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  have hcompute : ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) / 2 * ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16)
      = ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2) := by
    rw [div_eq_mul_inv, h2inv, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2)
      = ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) / 2 * ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16) :=
        hcompute.symm
    _ ≤ ENNReal.ofReal (((n : ℝ)⁻¹ / 2) ^ 2) / 2 * (1 - tvDist (P 0) (P ((n : ℝ)⁻¹))) :=
        mul_le_mul' le_rfl hcrux

end StatLean.Minimaxity
