import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Esseen's smoothing inequality and the univariate Berry–Esseen theorem

Mathlib (v4.29.1) contains neither Esseen's smoothing inequality nor the Berry–Esseen
theorem. This file builds them from scratch, following Feller, *An Introduction to
Probability Theory and Its Applications*, Vol. II, 2nd ed., Wiley, 1971, §XVI.3.

## Main results

* `norm_cexp_sub_taylor_le`, `norm_prod_sub_prod_le` — elementary complex-analytic
  estimates (restated here from `LindebergCLT.lean`, where they are `private`).
* Fejér-kernel facts and Esseen's smoothing inequality (in progress).

## Formalization notes

The two elementary estimates `norm_cexp_sub_taylor_le` (uniform third-order Taylor bound
for `exp (I y)`) and `norm_prod_sub_prod_le` (telescoping product bound) are needed both
here and in `LindebergCLT.lean`, where they are `private`. Rather than edit that file we
restate and reprove them verbatim, as the task requires.

**Reference.** W. Feller, *An Introduction to Probability Theory and Its Applications*,
Vol. II, 2nd ed., Wiley, 1971, §XVI.3 (smoothing) and §XVI.5 (Berry–Esseen).
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal Real

namespace StatLean.HypothesisTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Elementary complex-analytic estimates (restated from `LindebergCLT`) -/

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`.** The pointwise estimate driving
Lindeberg's swapping argument:
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both bounds are elementary: the cubic half comes from integrating the exponential's remainder
three times, the quadratic half from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality. Mathlib only provides the non-uniform `taylor_charFun_two`, so this is proved from
scratch here. -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  -- `|exp (I u)| = 1`.
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  -- Derivative of `u ↦ I u`.
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  -- Continuity of the three integrands.
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  -- Level 0: `‖exp (I z) − 1‖ ≤ z` for `z ≥ 0`.
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  -- Derivative of `A₁ w = exp (I w) − 1 − I w`.
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  -- Level 1: `‖exp (I z) − 1 − I z‖ ≤ z²/2` for `z ≥ 0`.
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  -- Derivative of `w ↦ w²/2` (written `w * w / 2`).
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  -- Derivative of `A₂ w = exp (I w) − 1 − I w + w²/2`.
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  -- `A₂ z` as an integral of `A₁ · I`.
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  -- The `y ≥ 0` case of the goal (with `|y| = y`).
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  -- Reduce the goal to `A₂`.
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · -- Reflect to `−y ≥ 0` via conjugation.
    have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz


/-- **Telescoping product bound** (restated from `LindebergCLT`). -/
private lemma norm_prod_sub_prod_le {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] (s : Finset ι)
    (f g : ι → 𝕜) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun i _ => norm_nonneg _) hg'
    have h1 : ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
      calc ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖
            ≤ 1 * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
              mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
        _ = ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := one_mul _
        _ ≤ ∑ i ∈ s, ‖f i - g i‖ := ih hf' hg'
    have h2 : ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ ≤ ‖f a - g a‖ :=
      calc ‖f a - g a‖ * ‖∏ i ∈ s, g i‖
            ≤ ‖f a - g a‖ * 1 := mul_le_mul_of_nonneg_left hpg (norm_nonneg _)
        _ = ‖f a - g a‖ := mul_one _
    linarith

/-! ### Characteristic-function Gaussian approximation

The analytic heart of Berry–Esseen: the characteristic function of a centered
square-integrable law with finite third moment is close to its second-order Taylor
polynomial `1 - v u²/2`, uniformly, with error `ρ|u|³/6`. This is `norm_cexp_sub_taylor_le`
integrated against the law, and needs no Fourier theory. -/

/-- **Second-order approximation of a characteristic function.** For a probability measure
`μ` on `ℝ` with mean `0`, second moment `v`, and finite third absolute moment `ρ = ∫|x|³`,
the characteristic function satisfies
`‖charFun μ u − (1 − v u²/2)‖ ≤ ρ |u|³ / 6` for all `u`. -/
theorem norm_charFun_sub_quadratic_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) (u : ℝ) :
    ‖charFun μ u - (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2)‖ ≤ (∫ x, |x| ^ 3 ∂μ) * |u| ^ 3 / 6 := by
  -- The complex exponential integrand of `charFun`.
  have hExpInt : Integrable (fun x : ℝ => Complex.exp (↑u * ↑x * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have hre : ((u : ℂ) * (x : ℂ) * I).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero]
  -- The quadratic Taylor integrand.
  set p : ℝ → ℂ := fun x => 1 + ↑u * ↑x * I - (↑u * ↑x) ^ 2 / 2 with hp
  have hxC : Integrable (fun x : ℝ => (x : ℂ)) μ := hint1.ofReal
  have hx2C : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) μ := hint2.ofReal
  have t2 : Integrable (fun x : ℝ => (↑u * ↑x * I : ℂ)) μ := by
    have := (hxC.const_mul (↑u * I : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); ring
  have t3 : Integrable (fun x : ℝ => ((↑u * ↑x) ^ 2 / 2 : ℂ)) μ := by
    have := (hx2C.const_mul (↑u ^ 2 / 2 : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); push_cast; ring
  have hPolyInt : Integrable p μ := by
    simp only [hp]; exact ((integrable_const (1 : ℂ)).add t2).sub t3
  -- Compute `∫ p = 1 - v u²/2`.
  have e1 : ∫ _x : ℝ, (1 : ℂ) ∂μ = 1 := by simp
  have e2 : ∫ x : ℝ, (↑u * ↑x * I : ℂ) ∂μ = 0 := by
    have hc : ∫ x : ℝ, (↑u * ↑x * I : ℂ) ∂μ = ∫ x : ℝ, ((↑u * I) • (↑x : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; ring
    rw [hc, integral_smul, integral_complex_ofReal, hmean]; simp
  have e3 : ∫ x : ℝ, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ = (v : ℂ) * (u : ℂ) ^ 2 / 2 := by
    have hc : ∫ x : ℝ, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ
        = ∫ x : ℝ, (((↑u : ℂ) ^ 2 / 2) • ((x ^ 2 : ℝ) : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; push_cast; ring
    rw [hc, integral_smul, integral_complex_ofReal, hvar, smul_eq_mul]; ring
  have hsum : Integrable (fun x : ℝ => (1 + ↑u * ↑x * I : ℂ)) μ :=
    ((integrable_const (1 : ℂ)).add t2).congr (ae_of_all _ fun x => rfl)
  have hIntP : ∫ x, p x ∂μ = 1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 := by
    calc ∫ x, p x ∂μ
        = ∫ x, ((1 + ↑u * ↑x * I : ℂ) - (↑u * ↑x) ^ 2 / 2) ∂μ := by simp only [hp]
      _ = (∫ x, (1 + ↑u * ↑x * I : ℂ) ∂μ) - ∫ x, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ :=
            integral_sub hsum t3
      _ = ((∫ _x : ℝ, (1 : ℂ) ∂μ) + ∫ x, (↑u * ↑x * I : ℂ) ∂μ)
            - ∫ x, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ := by
            rw [integral_add (integrable_const 1) t2]
      _ = 1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 := by rw [e1, e2, e3]; ring
  -- Pointwise Taylor bound.
  have hpt : ∀ x : ℝ, ‖Complex.exp (↑u * ↑x * I) - p x‖ ≤ |u| ^ 3 * |x| ^ 3 / 6 := by
    intro x
    have h := norm_cexp_sub_taylor_le (u * x)
    have harg : (↑u * ↑x * I : ℂ) = I * ↑(u * x) := by push_cast; ring
    have hsq : ((↑u * ↑x : ℂ)) ^ 2 = (↑(u * x) : ℂ) ^ 2 := by push_cast; ring
    rw [hp]; simp only []
    rw [harg, hsq]
    calc ‖Complex.exp (I * ↑(u * x)) - (1 + I * ↑(u * x) - (↑(u * x) : ℂ) ^ 2 / 2)‖
        ≤ min (|u * x| ^ 3 / 6) ((u * x) ^ 2) := h
      _ ≤ |u * x| ^ 3 / 6 := min_le_left _ _
      _ = |u| ^ 3 * |x| ^ 3 / 6 := by rw [abs_mul, mul_pow]
  -- Assemble.
  rw [charFun_apply_real, ← hIntP, ← integral_sub hExpInt hPolyInt]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : Integrable (fun x : ℝ => |u| ^ 3 * |x| ^ 3 / 6) μ := by
    have := (hint3.const_mul (|u| ^ 3)).div_const 6
    exact this
  calc ∫ x, ‖Complex.exp (↑u * ↑x * I) - p x‖ ∂μ
      ≤ ∫ x, |u| ^ 3 * |x| ^ 3 / 6 ∂μ :=
        integral_mono ((hExpInt.sub hPolyInt).norm) hbound hpt
    _ = (∫ x, |x| ^ 3 ∂μ) * |u| ^ 3 / 6 := by
        rw [integral_div, integral_const_mul]; ring

/-- **Quadratic upper bound for `e^{-z}`.** For `z ≥ 0`, `e^{-z} ≤ 1 - z + z²/2`. Combined
with `1 - z ≤ e^{-z}` (`Real.add_one_le_exp`) this pins `|e^{-z} - (1 - z)| ≤ z²/2`. -/
private lemma exp_neg_le_quadratic {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-z) ≤ 1 - z + z ^ 2 / 2 := by
  set f : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t) with hf
  have hderiv : ∀ x, HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2) (0 - 1 + 2 * x ^ 1 / 2) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 2 x).div_const 2)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have := h1.sub h2
    convert this using 1; ring
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hmono : Monotone f := monotone_of_deriv_nonneg hdiff fun x => by
    rw [(hderiv x).deriv]; linarith [Real.add_one_le_exp (-x)]
  have h0 : f 0 = 0 := by simp [hf]
  have hle := hmono hz
  rw [h0] at hle
  simp only [hf] at hle
  linarith

/-! ### Gaussian approximation of `charFun^n`

The characteristic function of an `n`-fold sum (which is `(charFun μ)^n` for a convolution)
compared to the Gaussian `exp(-n v w²/2)`. This packages steps (i)–(iii) of the classical
Berry–Esseen argument at the level of characteristic functions, with no Fourier theory. -/

/-- **Gaussian approximation of the `n`-th power of a characteristic function.** For a
centered law with second moment `v ≥ 0` and finite third moment,
`‖(charFun μ w)ⁿ − exp(−n v w²/2)‖ ≤ n·(ρ|w|³/6 + (v w²/2)²/2)`. Telescoping
(`norm_prod_sub_prod_le`) reduces to the single-factor bound
`‖charFun μ w − exp(−v w²/2)‖`, itself split into the Taylor error
(`norm_charFun_sub_quadratic_le`) and `‖(1 − z) − e^{−z}‖ ≤ z²/2`. -/
theorem norm_charFun_pow_sub_gaussian_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hv : 0 ≤ v) (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) (w : ℝ) (n : ℕ) :
    ‖(charFun μ w) ^ n - Complex.exp (-(n : ℂ) * v * w ^ 2 / 2)‖
      ≤ n * ((∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + (v * w ^ 2 / 2) ^ 2 / 2) := by
  set z : ℝ := v * w ^ 2 / 2 with hz_def
  have hznn : 0 ≤ z := by rw [hz_def]; positivity
  have hzc : (z : ℂ) = (v : ℂ) * (w : ℂ) ^ 2 / 2 := by rw [hz_def]; push_cast; ring
  -- Rewrite the Gaussian as `(exp(-z))ⁿ`.
  have hgauss : Complex.exp (-(n : ℂ) * v * w ^ 2 / 2) = (Complex.exp (-(z : ℂ))) ^ n := by
    rw [← Complex.exp_nat_mul]; congr 1; rw [hzc]; ring
  rw [hgauss]
  -- Both bases have norm ≤ 1.
  have hbase1 : ‖charFun μ w‖ ≤ 1 := norm_charFun_le_one w
  have hbase2 : ‖Complex.exp (-(z : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have : (-(z : ℂ)).re = -z := by simp
    rw [this]; exact Real.exp_le_one_iff.mpr (by linarith)
  -- Telescoping product bound.
  have htel : ‖(charFun μ w) ^ n - (Complex.exp (-(z : ℂ))) ^ n‖
      ≤ (n : ℝ) * ‖charFun μ w - Complex.exp (-(z : ℂ))‖ := by
    have hp := norm_prod_sub_prod_le (Finset.range n) (fun _ => charFun μ w)
      (fun _ => Complex.exp (-(z : ℂ))) (fun i _ => hbase1) (fun i _ => hbase2)
    simpa [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hp
  -- Single-factor bound.
  have hfac : ‖charFun μ w - Complex.exp (-(z : ℂ))‖
      ≤ (∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + z ^ 2 / 2 := by
    have h1 := norm_charFun_sub_quadratic_le μ hint1 hint2 hint3 hmean hvar w
    rw [← hzc] at h1
    -- `‖(1 - z) - exp(-z)‖ ≤ z²/2`.
    have hexpR : Complex.exp (-(z : ℂ)) = ((Real.exp (-z) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have h2 : ‖(1 - (z : ℂ)) - Complex.exp (-(z : ℂ))‖ ≤ z ^ 2 / 2 := by
      rw [hexpR]
      have hcast : (1 - (z : ℂ)) - ((Real.exp (-z) : ℝ) : ℂ)
          = ((1 - z - Real.exp (-z) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · linarith [exp_neg_le_quadratic hznn]
      · linarith [Real.add_one_le_exp (-z), sq_nonneg z]
    calc ‖charFun μ w - Complex.exp (-(z : ℂ))‖
        = ‖(charFun μ w - (1 - (z : ℂ))) + ((1 - (z : ℂ)) - Complex.exp (-(z : ℂ)))‖ := by
          ring_nf
      _ ≤ ‖charFun μ w - (1 - (z : ℂ))‖ + ‖(1 - (z : ℂ)) - Complex.exp (-(z : ℂ))‖ :=
          norm_add_le _ _
      _ ≤ (∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + z ^ 2 / 2 := add_le_add h1 h2
  calc ‖(charFun μ w) ^ n - (Complex.exp (-(z : ℂ))) ^ n‖
      ≤ (n : ℝ) * ‖charFun μ w - Complex.exp (-(z : ℂ))‖ := htel
    _ ≤ (n : ℝ) * ((∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + z ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = n * ((∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + (v * w ^ 2 / 2) ^ 2 / 2) := by rw [hz_def]

end StatLean.HypothesisTesting
