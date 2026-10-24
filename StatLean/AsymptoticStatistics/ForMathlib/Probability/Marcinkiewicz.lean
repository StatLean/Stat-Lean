/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic.ComputeDegree

/-!
# Marcinkiewicz's theorem

If a probability measure on `ℝ` has characteristic function `exp ∘ p` for a polynomial `p`,
then `deg p ≤ 2` (J. Marcinkiewicz, "Sur une propriété de la loi de Gauß", *Math. Z.* 44
(1939), 612–618). Combined with `Cumulant.eq_gaussianReal_of_cumulant_eq_zero` in
`CumulantCharFun.lean`, such a law is Gaussian (possibly degenerate). It is used in the proof of
Janson (1988, Theorem 2). It is unrelated to the Marcinkiewicz interpolation
theorem.

The proof is the classical one. The characteristic function extends to the entire function
`z ↦ exp (p (-i z))` once all exponential moments are finite (the analytic characteristic
function theorem, Lukacs 1970, Theorem 7.1.1); its modulus is maximized on the imaginary axis
along each horizontal line, which gives `Re p w ≤ Re p (i · Im w)`; and this polynomial
inequality forces `deg p ≤ 2`. Finiteness of all exponential moments is stated as
`integrableExpSet id μ = Set.univ`.

## Main results

* `degree_le_two_of_re_le_re_im`: the polynomial step.
* `re_eval_le_re_eval_im`: the ridge inequality.
* `hasAllExpMoments_of_charFun_eq_exp`: the analytic characteristic function theorem.
* `charFun_eq_exp_polynomial_degree_le_two`: Marcinkiewicz's theorem.
-/

open scoped ENNReal NNReal Nat
open Complex Filter Polynomial Real

namespace StatLean.AsymptoticStatistics

namespace Marcinkiewicz

/-! ### The polynomial step

The inequality `Re p w ≤ Re p (i · Im w)` for all `w` forces `deg p ≤ 2`. -/

section Endgame

/-- The real polynomial `r ↦ Re p(r w₁) - Re p(r w₂)`, whose `k`-th coefficient is
`(p.coeff k * w₁ ^ k).re - (p.coeff k * w₂ ^ k).re`. -/
private noncomputable def rayPoly (p : Polynomial ℂ) (w₁ w₂ : ℂ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    Polynomial.C ((p.coeff k * w₁ ^ k).re - (p.coeff k * w₂ ^ k).re) * Polynomial.X ^ k

private lemma rayPoly_degree_le (p : Polynomial ℂ) (w₁ w₂ : ℂ) :
    (rayPoly p w₁ w₂).degree ≤ (p.natDegree : WithBot ℕ) := by
  refine le_trans (Polynomial.degree_sum_le _ _) (Finset.sup_le fun k hk ↦ ?_)
  refine le_trans (Polynomial.degree_C_mul_X_pow_le k _) ?_
  exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

private lemma rayPoly_coeff_natDegree (p : Polynomial ℂ) (w₁ w₂ : ℂ) :
    (rayPoly p w₁ w₂).coeff p.natDegree =
      (p.coeff p.natDegree * w₁ ^ p.natDegree).re
        - (p.coeff p.natDegree * w₂ ^ p.natDegree).re := by
  rw [rayPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

private lemma rayPoly_eval (p : Polynomial ℂ) (w₁ w₂ : ℂ) (r : ℝ) :
    (rayPoly p w₁ w₂).eval r = (p.eval ((r : ℂ) * w₁)).re - (p.eval ((r : ℂ) * w₂)).re := by
  have key : ∀ w : ℂ, (p.eval ((r : ℂ) * w)).re
      = ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k * w ^ k).re * r ^ k := by
    intro w
    rw [Polynomial.eval_eq_sum_range, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hmul : p.coeff k * ((r : ℂ) * w) ^ k = (p.coeff k * w ^ k) * ((r ^ k : ℝ) : ℂ) := by
      push_cast; ring
    rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [key, key, rayPoly]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- If a real polynomial `P` is nonnegative on `ℝ` and `deg P ≤ n` with `n > 0`, then the
coefficient of `X ^ n` in `P` is nonnegative. -/
private lemma coeff_nonneg_of_eval_nonneg {P : Polynomial ℝ} {n : ℕ} (hn : 0 < n)
    (hdeg : P.degree ≤ (n : WithBot ℕ)) (hpos : ∀ r : ℝ, 0 ≤ P.eval r) : 0 ≤ P.coeff n := by
  by_contra hlt
  push Not at hlt
  have hne : P.coeff n ≠ 0 := ne_of_lt hlt
  have hdeg' : P.degree = (n : WithBot ℕ) :=
    Polynomial.degree_eq_of_le_of_coeff_ne_zero hdeg hne
  have hnat : P.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hdeg'
  have hlead : P.leadingCoeff ≤ 0 := by
    rw [Polynomial.leadingCoeff, hnat]; exact le_of_lt hlt
  have hdpos : 0 < P.degree := by rw [hdeg']; exact_mod_cast hn
  have := P.tendsto_atBot_of_leadingCoeff_nonpos hdpos hlead
  obtain ⟨r, hr⟩ := (this.eventually (eventually_lt_atBot 0)).exists
  exact absurd (hpos r) (not_le.mpr hr)

/-- If the real part of a complex polynomial `p` satisfies `Re p w ≤ Re p (i * Im w)` at
every `w`, then `deg p ≤ 2`. -/
theorem degree_le_two_of_re_le_re_im {p : Polynomial ℂ}
    (h : ∀ w : ℂ, (p.eval w).re ≤ (p.eval ((w.im : ℂ) * Complex.I)).re) :
    p.degree ≤ 2 := by
  by_contra hdeg
  push Not at hdeg
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp only [Polynomial.degree_zero] at hdeg
    exact absurd hdeg (by simp)
  set N := p.natDegree with hNdef
  have hdegN : p.degree = (N : WithBot ℕ) := Polynomial.degree_eq_natDegree hp0
  have hN3 : 3 ≤ N := by
    rw [hdegN] at hdeg
    have : (2 : ℕ) < N := by exact_mod_cast hdeg
    omega
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  set a := p.coeff N with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef, hNdef]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  -- choose `θ` with `a * exp (N θ I)` real and positive and `cos θ ≠ 0`; `N ≥ 3` allows this
  obtain ⟨θ, hθ, hcos⟩ :
      ∃ θ : ℝ, a * Complex.exp ((N : ℂ) * (θ : ℂ) * Complex.I) = (‖a‖ : ℂ)
        ∧ Real.cos θ ≠ 0 := by
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have harg : a = (‖a‖ : ℂ) * Complex.exp ((Complex.arg a : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I a).symm
    have key : ∀ m : ℤ, a * Complex.exp ((N : ℂ) *
        (((2 * π * m - Complex.arg a) / N : ℝ) : ℂ) * Complex.I) = (‖a‖ : ℂ) := by
      intro m
      have hcast : ((N : ℂ)) * (((2 * π * m - Complex.arg a) / N : ℝ) : ℂ)
          = ((2 * π * m : ℝ) : ℂ) - ((Complex.arg a : ℝ) : ℂ) := by
        push_cast
        field_simp
      have h2pi : Complex.exp (((2 * π * m : ℝ) : ℂ) * Complex.I) = 1 := by
        have hrw : (((2 * π * m : ℝ) : ℂ)) * Complex.I
            = (m : ℂ) * (2 * (π : ℂ) * Complex.I) := by push_cast; ring
        rw [hrw, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
      have hne : Complex.exp ((Complex.arg a : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      rw [hcast, sub_mul, Complex.exp_sub, h2pi, mul_one_div, div_eq_iff hne]
      exact harg
    by_cases h0 : Real.cos ((2 * π * (0 : ℤ) - Complex.arg a) / N) ≠ 0
    · exact ⟨_, key 0, h0⟩
    by_cases h1 : Real.cos ((2 * π * (1 : ℤ) - Complex.arg a) / N) ≠ 0
    · exact ⟨_, key 1, h1⟩
    -- otherwise `2π/N` would be a multiple of `π`, impossible for `N ≥ 3`
    exfalso
    push Not at h0 h1
    obtain ⟨k₀, hk₀⟩ := Real.cos_eq_zero_iff.mp h0
    obtain ⟨k₁, hk₁⟩ := Real.cos_eq_zero_iff.mp h1
    have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hd : 2 * π / (N : ℝ) = ((k₁ : ℝ) - k₀) * π := by
      have hL : (2 * π * ((1 : ℤ) : ℝ) - Complex.arg a) / N
          - (2 * π * ((0 : ℤ) : ℝ) - Complex.arg a) / N = 2 * π / (N : ℝ) := by
        push_cast
        field_simp
        ring
      rw [← hL, hk₀, hk₁]
      ring
    have hm : ((k₁ : ℝ) - k₀) = 2 / (N : ℝ) := by
      have h2 : ((k₁ : ℝ) - k₀) * π = (2 / (N : ℝ)) * π := by rw [← hd]; ring
      exact mul_right_cancel₀ Real.pi_ne_zero h2
    have hlt1 : ((k₁ : ℝ) - k₀) < 1 := by rw [hm, div_lt_one hNpos]; linarith
    have hgt0 : (0 : ℝ) < (k₁ : ℝ) - k₀ := by rw [hm]; positivity
    have hz : (0 : ℤ) < k₁ - k₀ := by
      have : (0 : ℝ) < ((k₁ - k₀ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hz1 : (1 : ℝ) ≤ ((k₁ - k₀ : ℤ) : ℝ) := by exact_mod_cast hz
    push_cast at hz1
    linarith
  -- the two rays
  set w₂ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hw₂
  set w₁ : ℂ := ((Real.sin θ : ℝ) : ℂ) * Complex.I with hw₁
  have him : ∀ r : ℝ, (((r : ℂ) * w₂).im : ℂ) * Complex.I = (r : ℂ) * w₁ := by
    intro r
    have him' : ((r : ℂ) * w₂).im = r * Real.sin θ := by
      rw [hw₂, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
    rw [him', hw₁]
    push_cast
    ring
  have hpos : ∀ r : ℝ, 0 ≤ (rayPoly p w₁ w₂).eval r := by
    intro r
    rw [rayPoly_eval]
    have := h ((r : ℂ) * w₂)
    rw [him r] at this
    linarith
  have hcN : 0 ≤ (a * w₁ ^ N).re - (a * w₂ ^ N).re := by
    have := coeff_nonneg_of_eval_nonneg (P := rayPoly p w₁ w₂) (n := N) (by omega)
      (rayPoly_degree_le p w₁ w₂) hpos
    rwa [rayPoly_coeff_natDegree, ← hadef, ← hNdef] at this
  -- evaluate the two top coefficients
  have h2 : (a * w₂ ^ N).re = ‖a‖ := by
    have hEq : a * w₂ ^ N = (‖a‖ : ℂ) := by
      rw [hw₂, ← Complex.exp_nat_mul, ← hθ]
      ring_nf
    rw [hEq, Complex.ofReal_re]
  have h1 : (a * w₁ ^ N).re = (Real.sin θ) ^ N * (a * Complex.I ^ N).re := by
    have hEq : a * w₁ ^ N = (a * Complex.I ^ N) * (((Real.sin θ) ^ N : ℝ) : ℂ) := by
      rw [hw₁, mul_pow]
      push_cast
      ring
    rw [hEq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm]
  rw [h1, h2] at hcN
  -- contradiction
  have hsin : |Real.sin θ| < 1 := by
    have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have hcpos : 0 < Real.cos θ ^ 2 := by positivity
    have hlt : Real.sin θ ^ 2 < 1 := by linarith
    exact (sq_lt_one_iff_abs_lt_one (Real.sin θ)).mp hlt
  have hbd : (Real.sin θ) ^ N * (a * Complex.I ^ N).re ≤ |Real.sin θ| ^ N * ‖a‖ := by
    calc (Real.sin θ) ^ N * (a * Complex.I ^ N).re
        ≤ |(Real.sin θ) ^ N * (a * Complex.I ^ N).re| := le_abs_self _
      _ = |Real.sin θ| ^ N * |(a * Complex.I ^ N).re| := by rw [abs_mul, abs_pow]
      _ ≤ |Real.sin θ| ^ N * ‖a * Complex.I ^ N‖ := by
          gcongr
          exact Complex.abs_re_le_norm _
      _ = |Real.sin θ| ^ N * ‖a‖ := by
          rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
  have hlt : |Real.sin θ| ^ N * ‖a‖ < ‖a‖ := by
    have : |Real.sin θ| ^ N < 1 := pow_lt_one₀ (abs_nonneg _) hsin (by omega)
    nlinarith
  linarith

end Endgame

/-! ### The ridge property

`ProbabilityTheory.norm_complexMGF_le_mgf` gives the ridge inequality once the characteristic
function is identified, by the identity theorem, with the two-sided Laplace transform on the
imaginary axis. -/

section Ridge

open MeasureTheory ProbabilityTheory

variable {μ : Measure ℝ} {p : Polynomial ℂ}

lemma analyticOnNhd_complexMGF_univ (h : integrableExpSet id μ = Set.univ) :
    AnalyticOnNhd ℂ (complexMGF id μ) Set.univ := fun z _ ↦
  analyticAt_complexMGF (by simp [h])

/-- If the characteristic function of `μ` is `exp ∘ p` on the real line and `μ` has all
exponential moments, then `z ↦ ∫ exp (z * x) dμ x` is the entire function `z ↦ exp (p (-i z))`,
by the identity theorem. -/
theorem complexMGF_eq_exp_eval (hmom : integrableExpSet id μ = Set.univ)
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) :
    complexMGF id μ = fun z ↦ Complex.exp (p.eval (-Complex.I * z)) := by
  have hdiff : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (p.eval (-Complex.I * z))) := by
    refine Complex.differentiable_exp.comp (p.differentiable.comp ?_)
    fun_prop
  have hG : AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.exp (p.eval (-Complex.I * z))) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := 0) (analyticOnNhd_complexMGF_univ hmom) hG ?_
  have hmap : Filter.Tendsto (fun t : ℝ ↦ (t : ℂ) * Complex.I)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun t : ℝ ↦ (t : ℂ) * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      simpa using ht
  refine hmap.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t ↦ ?_))
  have hz : -Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) := by
    linear_combination (-(t : ℂ)) * Complex.I_sq
  rw [complexMGF_id_mul_I, hp t, hz]

/-- **The ridge inequality.** If the characteristic function of `μ` is `exp ∘ p` on the real
line and its two-sided moment generating function is everywhere finite, then
`Re p w ≤ Re p (i · Im w)` for every complex `w`. -/
theorem re_eval_le_re_eval_im (hmom : integrableExpSet id μ = Set.univ)
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) (w : ℂ) :
    (p.eval w).re ≤ (p.eval ((w.im : ℂ) * Complex.I)).re := by
  have hF := complexMGF_eq_exp_eval hmom hp
  set z : ℂ := Complex.I * w with hzdef
  have hzre : ((z.re : ℝ) : ℂ) = -(w.im : ℂ) := by
    simp [hzdef, Complex.mul_re]
  have hz1 : -Complex.I * z = w := by
    rw [hzdef]; linear_combination (-w) * Complex.I_sq
  have hle : ‖complexMGF id μ z‖ ≤ mgf id μ z.re := norm_complexMGF_le_mgf
  simp only [hF] at hle
  have hLHS : ‖Complex.exp (p.eval (-Complex.I * z))‖ = Real.exp ((p.eval w).re) := by
    rw [Complex.norm_exp, hz1]
  have hRHS : mgf id μ z.re = Real.exp ((p.eval ((w.im : ℂ) * Complex.I)).re) := by
    have h0 : ((mgf id μ z.re : ℝ) : ℂ) = complexMGF id μ ((z.re : ℝ) : ℂ) :=
      (complexMGF_ofReal _).symm
    simp only [hF] at h0
    have h1 : -Complex.I * ((z.re : ℝ) : ℂ) = ((w.im : ℝ) : ℂ) * Complex.I := by
      rw [hzre]; ring
    rw [h1] at h0
    have h2 := congrArg norm h0
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg mgf_nonneg, Complex.norm_exp] at h2
  rw [hLHS, hRHS] at hle
  exact Real.exp_le_exp.mp hle

/-- Marcinkiewicz's theorem under the additional hypothesis that all exponential moments are
finite. -/
theorem degree_le_two_of_hasAllExpMoments (hmom : integrableExpSet id μ = Set.univ)
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) :
    p.degree ≤ 2 :=
  degree_le_two_of_re_le_re_im (re_eval_le_re_eval_im hmom hp)

end Ridge

/-! ### The analytic characteristic function theorem: moments

The induction uses the oscillating integrals
`momInt μ (2 n) t = ∫ x ^ (2 n) exp (i t x) dμ`, which `MeasureTheory.iteratedDeriv_charFun`
identifies with `± iteratedDeriv (2 n) (charFun μ) t`. -/

section StepA

open MeasureTheory ProbabilityTheory

/-- The second difference quotient `(2 - 2 cos (h x)) / h ^ 2` converges to `x ^ 2` as
`h ↓ 0`, with the rate given by `Real.cos_bound`. -/
lemma tendsto_two_sub_two_cos_div_sq (x : ℝ) :
    Filter.Tendsto (fun h : ℝ ↦ (2 - 2 * Real.cos (h * x)) / h ^ 2)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (x ^ 2)) := by
  have hδ : (0 : ℝ) < 1 / (|x| + 1) := by positivity
  have hkey : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |(2 - 2 * Real.cos (h * x)) / h ^ 2 - x ^ 2| ≤ (5 / 48) * x ^ 4 * h ^ 2 := by
    have hmem : Set.Iio (1 / (|x| + 1)) ∈ nhds (0 : ℝ) := Iio_mem_nhds hδ
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with h hh0 hhδ
    replace hh0 : (0 : ℝ) < h := hh0
    replace hhδ : h < 1 / (|x| + 1) := hhδ
    have hx1 : |h * x| ≤ 1 := by
      rw [abs_mul, abs_of_pos hh0]
      have h1 : h * (|x| + 1) < (1 / (|x| + 1)) * (|x| + 1) :=
        mul_lt_mul_of_pos_right hhδ (by positivity)
      have h2 : (1 / (|x| + 1)) * (|x| + 1) = 1 := by field_simp
      have h3 : h * |x| ≤ h * (|x| + 1) := by nlinarith [abs_nonneg x, hh0]
      linarith
    have hb := Real.cos_bound hx1
    have hne : h ^ 2 ≠ 0 := by positivity
    have hrw : (2 - 2 * Real.cos (h * x)) / h ^ 2 - x ^ 2
        = -2 * (Real.cos (h * x) - (1 - (h * x) ^ 2 / 2)) / h ^ 2 := by
      field_simp
      ring
    rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < h ^ 2)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < h ^ 2)]
    have hb' : |(-2 : ℝ) * (Real.cos (h * x) - (1 - (h * x) ^ 2 / 2))|
        ≤ 2 * (|h * x| ^ 4 * (5 / 96)) := by
      rw [abs_mul]
      simp only [abs_neg, abs_two]
      linarith [hb]
    have hpow : |h * x| ^ 4 = h ^ 4 * x ^ 4 := by
      rw [abs_mul, mul_pow, abs_of_pos hh0]
      congr 1
      rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    rw [hpow] at hb'
    exact hb'.trans_eq (by ring)
  have hlim : Filter.Tendsto (fun h : ℝ ↦ (5 / 48) * x ^ 4 * h ^ 2)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
    have hc : Continuous (fun h : ℝ ↦ (5 / 48) * x ^ 4 * h ^ 2) := by fun_prop
    have h0 : Filter.Tendsto (fun h : ℝ ↦ (5 / 48) * x ^ 4 * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using hc.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hsub : Filter.Tendsto (fun h : ℝ ↦ (2 - 2 * Real.cos (h * x)) / h ^ 2 - x ^ 2)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
    squeeze_zero_norm' (by filter_upwards [hkey] with h hh using hh) hlim
  have := hsub.add (tendsto_const_nhds (x := x ^ 2)
    (f := nhdsWithin (0 : ℝ) (Set.Ioi 0)))
  simpa using this

/-- If the second symmetric difference at `0` of `t ↦ ∫ g x * exp (i t x) dν` is `O (h ^ 2)`
as `h ↓ 0`, then `g * x ^ 2` is `ν`-integrable (by Fatou's lemma). -/
lemma integrable_mul_sq_of_second_difference {ν : Measure ℝ} {g : ℝ → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hgm : Measurable g) (hgi : Integrable g ν) {C : ℝ}
    (hb : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∫ x, g x * (2 - 2 * Real.cos (h * x)) ∂ν ≤ C * h ^ 2) :
    Integrable (fun x ↦ g x * x ^ 2) ν := by
  set F : ℝ → ℝ → ℝ := fun h x ↦ g x * ((2 - 2 * Real.cos (h * x)) / h ^ 2) with hF
  -- every `F h` is nonnegative, measurable and integrable
  have hcos : ∀ h x : ℝ, 0 ≤ 2 - 2 * Real.cos (h * x) := by
    intro h x; nlinarith [Real.cos_le_one (h * x)]
  have hFnn : ∀ h x : ℝ, 0 ≤ F h x := fun h x ↦
    mul_nonneg (hg x) (div_nonneg (hcos h x) (sq_nonneg h))
  have hFm : ∀ h : ℝ, Measurable (F h) := by
    intro h
    rw [hF]
    fun_prop
  -- Fatou's lemma
  have hfatou : ∫⁻ x, ENNReal.ofReal (g x * x ^ 2) ∂ν
      ≤ Filter.liminf (fun h ↦ ∫⁻ x, ENNReal.ofReal (F h x) ∂ν)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    have hpt : ∀ x : ℝ, Filter.liminf (fun h ↦ ENNReal.ofReal (F h x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) = ENNReal.ofReal (g x * x ^ 2) := by
      intro x
      refine Filter.Tendsto.liminf_eq ?_
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_two_sub_two_cos_div_sq x).const_mul (g x)))
    calc ∫⁻ x, ENNReal.ofReal (g x * x ^ 2) ∂ν
        = ∫⁻ x, Filter.liminf (fun h ↦ ENNReal.ofReal (F h x))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ∂ν := by
          simp_rw [hpt]
      _ ≤ _ := lintegral_liminf_le (fun h ↦ (hFm h).ennreal_ofReal)
  -- each `∫⁻ F h` is at most `ofReal C`, eventually
  have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∫⁻ x, ENNReal.ofReal (F h x) ∂ν ≤ ENNReal.ofReal C := by
    filter_upwards [hb, self_mem_nhdsWithin] with h hbh hh0
    have hh0' : (0 : ℝ) < h := hh0
    have hint : Integrable (F h) ν := by
      refine Integrable.mono' (hgi.const_mul (4 / h ^ 2)) ((hFm h).aestronglyMeasurable) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn h x), hF]
      have h4 : 2 - 2 * Real.cos (h * x) ≤ 4 := by nlinarith [Real.neg_one_le_cos (h * x)]
      have : g x * ((2 - 2 * Real.cos (h * x)) / h ^ 2) ≤ g x * (4 / h ^ 2) := by
        gcongr
        exact hg x
      calc g x * ((2 - 2 * Real.cos (h * x)) / h ^ 2) ≤ g x * (4 / h ^ 2) := this
        _ = 4 / h ^ 2 * g x := by ring
    have hval : ∫ x, F h x ∂ν ≤ C := by
      have hsplit : ∫ x, F h x ∂ν = (∫ x, g x * (2 - 2 * Real.cos (h * x)) ∂ν) / h ^ 2 := by
        rw [hF, ← integral_div]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
      rw [hsplit, div_le_iff₀ (by positivity : (0 : ℝ) < h ^ 2)]
      calc ∫ x, g x * (2 - 2 * Real.cos (h * x)) ∂ν ≤ C * h ^ 2 := hbh
        _ = C * h ^ 2 := rfl
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (hFnn h))]
    exact ENNReal.ofReal_le_ofReal hval
  have hle : ∫⁻ x, ENNReal.ofReal (g x * x ^ 2) ∂ν ≤ ENNReal.ofReal C :=
    hfatou.trans (Filter.liminf_le_of_frequently_le' (hev.frequently))
  refine ⟨(hgm.mul (measurable_id.pow_const 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x ↦
    mul_nonneg (hg x) (by positivity))]
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top


/-- A form of the mean value inequality on the segment from `0` to `y`, valid on both sides
of `0`, with the derivative bounded only on that segment. -/
private lemma norm_sub_zero_le_of_deriv_bound {F F' : ℝ → ℂ} {M y : ℝ}
    (hd : ∀ x, HasDerivAt F (F' x) x) (hb : ∀ x, |x| ≤ |y| → ‖F' x‖ ≤ M) :
    ‖F y - F 0‖ ≤ M * |y| := by
  rcases le_or_gt (0 : ℝ) y with hy0 | hy0
  · have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := F) (f' := F') (a := 0) (b := y) (fun x _ ↦ (hd x).hasDerivWithinAt)
      (fun x hx ↦ hb x (by
        rw [abs_of_nonneg hx.1, abs_of_nonneg hy0]
        exact le_of_lt hx.2)) y (Set.right_mem_Icc.mpr hy0)
    rw [abs_of_nonneg hy0]
    simpa using hmv
  · have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := F) (f' := F') (a := y) (b := 0) (fun x _ ↦ (hd x).hasDerivWithinAt)
      (fun x hx ↦ hb x (by
        rw [abs_of_nonpos (le_of_lt hx.2), abs_of_neg hy0]
        linarith [hx.1])) 0 (Set.right_mem_Icc.mpr (le_of_lt hy0))
    rw [abs_of_neg hy0, ← norm_neg, neg_sub]
    simpa using hmv

/-- The second symmetric difference at `0` of a twice-differentiable function with continuous
second derivative is `O (h ^ 2)` on `[-1, 1]`. The proof uses the first-order Taylor remainder
`s ↦ F s - F 0 - s • F' 0`. -/
lemma norm_second_difference_le {f : ℝ → ℂ} (h1 : Differentiable ℝ f)
    (h2 : Differentiable ℝ (deriv f)) (h3 : Continuous (deriv (deriv f))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ 1 → ‖2 * f 0 - f h - f (-h)‖ ≤ C * h ^ 2 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    h3.continuousOn
  set M' := max M 0 with hM'def
  have hM'0 : (0 : ℝ) ≤ M' := le_max_right _ _
  have hMb : ∀ x : ℝ, |x| ≤ 1 → ‖deriv (deriv f) x‖ ≤ M' := fun x hx ↦
    (hM x (abs_le.mp hx)).trans (le_max_left _ _)
  have hincr : ∀ y : ℝ, |y| ≤ 1 → ‖deriv f y - deriv f 0‖ ≤ M' * |y| := by
    intro y hy
    exact norm_sub_zero_le_of_deriv_bound (fun x ↦ ((h2 x).hasDerivAt))
      (fun x hx ↦ hMb x (hx.trans hy))
  set taylorRem : ℝ → ℂ := fun s ↦ f s - f 0 - s • deriv f 0 with htaylorRemdef
  have htaylorRemd : ∀ s : ℝ, HasDerivAt taylorRem (deriv f s - deriv f 0) s := by
    intro s
    have hA : HasDerivAt (fun y : ℝ ↦ f y) (deriv f s) s := (h1 s).hasDerivAt
    have hB := (hasDerivAt_id s).smul_const (deriv f 0)
    rw [one_smul] at hB
    exact (hA.sub_const (f 0)).sub hB
  have htaylorRem0 : taylorRem 0 = 0 := by simp [htaylorRemdef]
  have hTaylor : ∀ y : ℝ, |y| ≤ 1 → ‖taylorRem y‖ ≤ M' * |y| * |y| := by
    intro y hy
    have hbnd : ∀ x : ℝ, |x| ≤ |y| → ‖deriv f x - deriv f 0‖ ≤ M' * |y| := by
      intro x hx
      exact (hincr x (hx.trans hy)).trans (by nlinarith [abs_nonneg x, abs_nonneg y])
    have := norm_sub_zero_le_of_deriv_bound (F := taylorRem) (M := M' * |y|) htaylorRemd hbnd
    rwa [htaylorRem0, sub_zero] at this
  refine ⟨2 * M', by positivity, ?_⟩
  intro h hh
  have hah : |(-h : ℝ)| = |h| := abs_neg h
  have hsum : 2 * f 0 - f h - f (-h) = -(taylorRem h + taylorRem (-h)) := by
    simp only [htaylorRemdef, Complex.real_smul]
    push_cast
    ring
  rw [hsum, norm_neg]
  calc ‖taylorRem h + taylorRem (-h)‖ ≤ ‖taylorRem h‖ + ‖taylorRem (-h)‖ := norm_add_le _ _
    _ ≤ M' * |h| * |h| + M' * |(-h : ℝ)| * |(-h : ℝ)| := by
        gcongr
        · exact hTaylor h hh
        · exact hTaylor (-h) (by rwa [hah])
    _ = 2 * M' * h ^ 2 := by
        rw [hah]
        linear_combination (2 * M') * abs_mul_abs_self h

/-- The `m`-th moment integral of `μ` against the oscillating factor, i.e. the integral whose
value `MeasureTheory.iteratedDeriv_charFun` identifies with a derivative of `charFun μ`. -/
private noncomputable def momInt (μ : Measure ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) ^ m * Complex.exp (t * x * Complex.I) ∂μ

private lemma integrable_momInt {μ : Measure ℝ} {n : ℕ}
    (hint : Integrable (fun x : ℝ ↦ x ^ (2 * n)) μ) (t : ℝ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ (2 * n) * Complex.exp (t * x * Complex.I)) μ := by
  refine Integrable.mono' hint (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg]
  rw [pow_mul]
  positivity

/-- The second symmetric difference of `momInt μ (2 n)` at `0` is the real integral
`∫ x ^ (2 n) * (2 - 2 cos (h x))`. -/
private lemma momInt_second_difference {μ : Measure ℝ} {n : ℕ}
    (hint : Integrable (fun x : ℝ ↦ x ^ (2 * n)) μ) (h : ℝ) :
    ((∫ x : ℝ, x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) ∂μ : ℝ) : ℂ)
      = 2 * momInt μ (2 * n) 0 - momInt μ (2 * n) h - momInt μ (2 * n) (-h) := by
  have hptwise : ∀ x : ℝ, ((x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) : ℝ) : ℂ)
      = 2 * ((x : ℂ) ^ (2 * n) * Complex.exp (((0 : ℝ) : ℂ) * x * Complex.I))
        - (x : ℂ) ^ (2 * n) * Complex.exp ((h : ℂ) * x * Complex.I)
        - (x : ℂ) ^ (2 * n) * Complex.exp (((-h : ℝ) : ℂ) * x * Complex.I) := by
    intro x
    have e0 : Complex.exp (((0 : ℝ) : ℂ) * (x : ℂ) * Complex.I) = 1 := by
      norm_num
    have ecos : Complex.exp ((h : ℂ) * (x : ℂ) * Complex.I)
        + Complex.exp (((-h : ℝ) : ℂ) * (x : ℂ) * Complex.I)
        = 2 * ((Real.cos (h * x) : ℝ) : ℂ) := by
      have hA : (h : ℂ) * (x : ℂ) = ((h * x : ℝ) : ℂ) := by push_cast; ring
      have hB : ((-h : ℝ) : ℂ) * (x : ℂ) = -(((h * x : ℝ)) : ℂ) := by push_cast; ring
      rw [hA, hB, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        Complex.ofReal_cos]
      ring
    push_cast at e0 ecos ⊢
    linear_combination (-2 * (x : ℂ) ^ (2 * n)) * e0 + ((x : ℂ) ^ (2 * n)) * ecos
  rw [← integral_complex_ofReal]
  simp_rw [hptwise]
  rw [integral_sub (by
        exact ((integrable_momInt hint 0).const_mul 2).sub (integrable_momInt hint h))
      (integrable_momInt hint (-h)),
    integral_sub ((integrable_momInt hint 0).const_mul 2) (integrable_momInt hint h),
    integral_const_mul]
  rfl


/-- `Integrable (x ^ (2 m))` implies `MemLp id (2 m)`, the hypothesis of
`MeasureTheory.iteratedDeriv_charFun`. -/
private lemma memLp_id_of_integrable_pow {μ : Measure ℝ} {m : ℕ}
    (hint : Integrable (fun x : ℝ ↦ x ^ (2 * m)) μ) : MemLp id ((2 * m : ℕ) : ℝ≥0∞) μ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using memLp_zero_iff_aestronglyMeasurable.mpr aestronglyMeasurable_id
  · have hp0 : ((2 * m : ℕ) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hpt : ((2 * m : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    rw [← integrable_norm_rpow_iff aestronglyMeasurable_id hp0 hpt]
    have hcast : (((2 * m : ℕ) : ℝ≥0∞)).toReal = ((2 * m : ℕ) : ℝ) := by simp
    rw [hcast]
    have heq : ∀ x : ℝ, ‖id x‖ ^ ((2 * m : ℕ) : ℝ) = x ^ (2 * m) := by
      intro x
      rw [id_eq, Real.norm_eq_abs, Real.rpow_natCast, ← abs_pow, abs_of_nonneg]
      rw [pow_mul]
      positivity
    simp_rw [heq]
    exact hint

private lemma iteratedDeriv_charFun_eq_momInt {μ : Measure ℝ} [IsFiniteMeasure μ] {n : ℕ}
    (hint : Integrable (fun x : ℝ ↦ x ^ (2 * n)) μ) (t : ℝ) :
    iteratedDeriv (2 * n) (charFun μ) t = (-1 : ℂ) ^ n * momInt μ (2 * n) t := by
  rw [MeasureTheory.iteratedDeriv_charFun (memLp_id_of_integrable_pow hint), momInt, pow_mul,
    Complex.I_sq]

/-- `exp ∘ p` is smooth as a function `ℝ → ℂ`, being the restriction of an entire function. -/
private lemma contDiff_exp_eval (p : Polynomial ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun t : ℝ ↦ Complex.exp (p.eval (t : ℂ))) := by
  have hdiff : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (p.eval z)) :=
    Complex.differentiable_exp.comp p.differentiable
  exact (hdiff.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-- All moments of `μ` are finite when its characteristic function is `exp ∘ p`; the
`(2 n)`-th derivative of `charFun μ` yields the `(2 n + 2)`-nd moment. -/
theorem integrable_pow_two_mul {μ : Measure ℝ} [IsProbabilityMeasure μ] {p : Polynomial ℂ}
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ (2 * n)) μ := by
  have hfun : charFun μ = fun t : ℝ ↦ Complex.exp (p.eval (t : ℂ)) := funext hp
  have hCD : ∀ k : WithTop ℕ∞, ContDiff ℝ k (charFun μ) := by
    intro k
    rw [hfun]
    exact contDiff_exp_eval p
  induction n with
  | zero => simp
  | succ n ih =>
    set ψ := iteratedDeriv (2 * n) (charFun μ) with hψ
    have hd1 : Differentiable ℝ ψ := by
      rw [hψ]
      exact ContDiff.differentiable_iteratedDeriv' (2 * n) (hCD _)
    have hd2 : Differentiable ℝ (deriv ψ) := by
      rw [hψ, ← iteratedDeriv_succ]
      exact ContDiff.differentiable_iteratedDeriv' (2 * n + 1) (hCD _)
    have hd3 : Continuous (deriv (deriv ψ)) := by
      rw [hψ, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
      exact ContDiff.continuous_iteratedDeriv' (2 * n + 1 + 1) (hCD _)
    obtain ⟨C, hC0, hCb⟩ := norm_second_difference_le hd1 hd2 hd3
    have hsq : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hmom : ∀ t : ℝ, momInt μ (2 * n) t = (-1 : ℂ) ^ n * ψ t := by
      intro t
      have hd := iteratedDeriv_charFun_eq_momInt ih t
      rw [← hψ] at hd
      rw [hd, ← mul_assoc, hsq, one_mul]
    have hbound : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∫ x, x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) ∂μ ≤ C * h ^ 2 := by
      have hmem : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with h hh0 hh1
      replace hh0 : (0 : ℝ) < h := hh0
      replace hh1 : h < 1 := hh1
      have habs : |h| ≤ 1 := by rw [abs_of_pos hh0]; linarith
      have hchain : ((∫ x : ℝ, x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) ∂μ : ℝ) : ℂ)
          = (-1 : ℂ) ^ n * (2 * ψ 0 - ψ h - ψ (-h)) := by
        rw [momInt_second_difference ih h, hmom, hmom, hmom]
        ring
      have hnorm : |∫ x : ℝ, x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) ∂μ|
          = ‖2 * ψ 0 - ψ h - ψ (-h)‖ := by
        have hc := congrArg norm hchain
        rwa [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, norm_neg, norm_one,
          one_pow, one_mul] at hc
      calc ∫ x : ℝ, x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) ∂μ
          ≤ |∫ x : ℝ, x ^ (2 * n) * (2 - 2 * Real.cos (h * x)) ∂μ| := le_abs_self _
        _ = ‖2 * ψ 0 - ψ h - ψ (-h)‖ := hnorm
        _ ≤ C * h ^ 2 := hCb h habs
    have hres := integrable_mul_sq_of_second_difference (ν := μ) (g := fun x : ℝ ↦ x ^ (2 * n))
      (fun x ↦ by rw [pow_mul]; positivity) (by fun_prop) ih hbound
    have heq : (fun x : ℝ ↦ x ^ (2 * n) * x ^ 2) = fun x : ℝ ↦ x ^ (2 * (n + 1)) := by
      funext x
      rw [← pow_add]
      ring_nf
    rwa [heq] at hres

/-- Every moment of `μ` is finite, in the `MemLp` form. -/
theorem memLp_id_of_charFun_eq_exp {μ : Measure ℝ} [IsProbabilityMeasure μ] {p : Polynomial ℂ}
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) (m : ℕ) :
    MemLp id (m : ℝ≥0∞) μ := by
  have h2 := memLp_id_of_integrable_pow (integrable_pow_two_mul hp m)
  refine h2.mono_exponent ?_
  exact_mod_cast Nat.le_mul_of_pos_left m (by norm_num)

end StepA

/-! ### The analytic characteristic function theorem: exponential moments -/

section Gap

open MeasureTheory ProbabilityTheory

variable {μ : Measure ℝ} {p : Polynomial ℂ}

/-- For an entire `G`, the normalized derivatives `‖iteratedDeriv k G 0‖ / k !` are summable
against `a ^ k` for every `a`. -/
private lemma summable_iteratedDeriv_div_factorial {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun k : ℕ ↦ ‖iteratedDeriv k G 0‖ / (k ! : ℝ) * a ^ k) := by
  have hps0 : HasFPowerSeriesOnBall G (cauchyPowerSeries G 0 1) 0 ⊤ :=
    hG.hasFPowerSeriesOnBall (R := 1) 0 (by norm_num)
  obtain ⟨P, hps⟩ : ∃ P, HasFPowerSeriesOnBall G P 0 ⊤ := ⟨_, hps0⟩
  have hlt : ((a.toNNReal : ℝ≥0) : ℝ≥0∞) < P.radius :=
    lt_of_lt_of_le ENNReal.coe_lt_top hps.r_le
  have hsum : Summable (fun k : ℕ ↦ ‖P k‖ * ((a.toNNReal : ℝ≥0) : ℝ) ^ k) :=
    P.summable_norm_mul_pow hlt
  rw [Real.coe_toNNReal a ha] at hsum
  refine hsum.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
  have hfac : (0 : ℝ) < (k ! : ℝ) := by positivity
  have hkey : ‖iteratedDeriv k G 0‖ ≤ (k ! : ℝ) * ‖P k‖ := by
    have hfs := hps.factorial_smul (y := (1 : ℂ)) k
    have hid : iteratedDeriv k G 0 = iteratedFDeriv ℂ k G 0 (fun _ ↦ 1) :=
      iteratedDeriv_eq_iteratedFDeriv
    have hop : ‖P k (fun _ : Fin k ↦ (1 : ℂ))‖ ≤ ‖P k‖ := by
      simp
    rw [hid, ← hfs, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hop (by positivity)
  calc ‖iteratedDeriv k G 0‖ / (k ! : ℝ) * a ^ k
      ≤ ((k ! : ℝ) * ‖P k‖) / (k ! : ℝ) * a ^ k := by gcongr
    _ = ‖P k‖ * a ^ k := by field_simp

/-- **Analytic characteristic function theorem.** A probability measure whose characteristic
function is `exp ∘ p` on the real line has a finite two-sided moment generating function at
every real argument. -/
theorem hasAllExpMoments_of_charFun_eq_exp [IsProbabilityMeasure μ]
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) :
    integrableExpSet id μ = Set.univ := by
  refine Set.eq_univ_of_forall fun c ↦ ?_
  change Integrable (fun x : ℝ ↦ Real.exp (c * x)) μ
  set G : ℂ → ℂ := fun z ↦ Complex.exp (p.eval z) with hGdef
  have hG : Differentiable ℂ G := Complex.differentiable_exp.comp p.differentiable
  have hGd : ∀ k : ℕ, Differentiable ℂ (iteratedDeriv k G) := by
    intro k
    induction k with
    | zero => simpa using hG
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hfun : charFun μ = fun t : ℝ ↦ G (t : ℂ) := funext hp
  -- iterated derivatives of the restriction are the restrictions of the iterated derivatives
  have hrestrict : ∀ k : ℕ, ∀ t : ℝ,
      iteratedDeriv k (fun s : ℝ ↦ G (s : ℂ)) t = iteratedDeriv k G (t : ℂ) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfe : iteratedDeriv k (fun s : ℝ ↦ G (s : ℂ))
          = fun s : ℝ ↦ iteratedDeriv k G (s : ℂ) := funext ih
      rw [hfe]
      exact (((hGd k) (t : ℂ)).hasDerivAt.comp_ofReal).deriv
  -- the even moments are the derivatives of `G` at `0`
  have hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ (2 * n) ∂μ = ‖iteratedDeriv (2 * n) G 0‖ := by
    intro n
    have hnn : (0 : ℝ) ≤ ∫ x : ℝ, x ^ (2 * n) ∂μ := by
      refine integral_nonneg fun x ↦ ?_
      rw [pow_mul]
      positivity
    have hd := MeasureTheory.iteratedDeriv_charFun_zero
      (memLp_id_of_integrable_pow (integrable_pow_two_mul hp n))
    have hz : iteratedDeriv (2 * n) G 0 = iteratedDeriv (2 * n) (charFun μ) 0 := by
      rw [hfun, hrestrict (2 * n) 0]
      norm_num
    rw [hz, hd, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  -- the series of moments converges
  set F : ℕ → ℝ := fun k ↦ ‖iteratedDeriv k G 0‖ / (k ! : ℝ) * |c| ^ k with hFdef
  have hFsummable : Summable F := summable_iteratedDeriv_div_factorial hG (abs_nonneg c)
  have hFeven : Summable (fun n : ℕ ↦ F (2 * n)) := by
    have hinj : Function.Injective (fun n : ℕ ↦ 2 * n) :=
      mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
    exact hFsummable.comp_injective hinj
  have hFnn : ∀ k, 0 ≤ F k := fun k ↦ by rw [hFdef]; positivity
  -- each term of the `cosh` series integrates to a term of that series
  have hterm : ∀ n : ℕ, ∫ x : ℝ, (c * x) ^ (2 * n) / ((2 * n)! : ℝ) ∂μ = F (2 * n) := by
    intro n
    have hcast : ∀ x : ℝ, (c * x) ^ (2 * n) / ((2 * n)! : ℝ)
        = (c ^ (2 * n) / ((2 * n)! : ℝ)) * x ^ (2 * n) := by
      intro x; rw [mul_pow]; ring
    simp_rw [hcast]
    have hcabs : |c| ^ (2 * n) = c ^ (2 * n) := by
      rw [← abs_pow, abs_of_nonneg]
      rw [pow_mul]
      positivity
    rw [integral_const_mul, hmom n]
    change c ^ (2 * n) / ((2 * n)! : ℝ) * ‖iteratedDeriv (2 * n) G 0‖
      = ‖iteratedDeriv (2 * n) G 0‖ / ((2 * n)! : ℝ) * |c| ^ (2 * n)
    rw [hcabs]
    ring
  -- the `cosh` series, integrated term by term
  have hlint : ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (c * x)) ∂μ
      ≤ ENNReal.ofReal (∑' n : ℕ, F (2 * n)) := by
    have hstep1 : ∀ x : ℝ, ENNReal.ofReal (Real.cosh (c * x))
        = ∑' n : ℕ, ENNReal.ofReal ((c * x) ^ (2 * n) / ((2 * n)! : ℝ)) := by
      intro x
      rw [← (Real.hasSum_cosh (c * x)).tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by rw [pow_mul]; positivity)
        (Real.hasSum_cosh (c * x)).summable
    calc ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (c * x)) ∂μ
        = ∫⁻ x : ℝ, ∑' n : ℕ, ENNReal.ofReal ((c * x) ^ (2 * n) / ((2 * n)! : ℝ)) ∂μ := by
          simp_rw [hstep1]
      _ = ∑' n : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal ((c * x) ^ (2 * n) / ((2 * n)! : ℝ)) ∂μ :=
          lintegral_tsum (fun n ↦ by fun_prop)
      _ = ∑' n : ℕ, ENNReal.ofReal (F (2 * n)) := by
          refine tsum_congr fun n ↦ ?_
          rw [← hterm n]
          refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
          · have hI := (integrable_pow_two_mul hp n).const_mul (c ^ (2 * n) / ((2 * n)! : ℝ))
            refine hI.congr (Filter.Eventually.of_forall fun x ↦ ?_)
            change c ^ (2 * n) / ((2 * n)! : ℝ) * x ^ (2 * n)
              = (c * x) ^ (2 * n) / ((2 * n)! : ℝ)
            rw [mul_pow]
            ring
          · filter_upwards with x
            rw [pow_mul]
            positivity
      _ ≤ ENNReal.ofReal (∑' n : ℕ, F (2 * n)) :=
          le_of_eq (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ hFnn _) hFeven).symm
  have hcoshint : Integrable (fun x : ℝ ↦ Real.cosh (c * x)) μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x ↦ (Real.cosh_pos _).le)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine Integrable.mono' (hcoshint.const_mul 2) (by fun_prop)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.cosh_eq]
  have hpos := Real.exp_pos (-(c * x))
  linarith

/-- **Marcinkiewicz (1939).** If the characteristic function of a
probability measure on `ℝ` is `exp ∘ p` for a polynomial `p`, then `deg p ≤ 2`. -/
theorem charFun_eq_exp_polynomial_degree_le_two [IsProbabilityMeasure μ]
    (hp : ∀ t : ℝ, charFun μ t = Complex.exp (p.eval (t : ℂ))) :
    p.degree ≤ 2 :=
  degree_le_two_of_hasAllExpMoments (hasAllExpMoments_of_charFun_eq_exp hp) hp

end Gap

/-! ### Examples

The exponent `- t ^ 2 / 2` of the standard Gaussian characteristic function has degree exactly
`2`, and `exp (- t ^ 4)` is shown not to be a characteristic function. -/

section Witness

open MeasureTheory ProbabilityTheory

/-- The polynomial `- X ^ 2 / 2`, whose exponential is the standard Gaussian characteristic
function. -/
noncomputable def gaussPoly : Polynomial ℂ := Polynomial.C (-1 / 2 : ℂ) * Polynomial.X ^ 2

lemma gaussPoly_eval (t : ℂ) : gaussPoly.eval t = -t ^ 2 / 2 := by
  simp [gaussPoly]; ring

/-- The Gaussian polynomial has degree exactly `2`. -/
theorem gaussPoly_degree : gaussPoly.degree = 2 := by
  rw [gaussPoly]
  compute_degree!

/-- `exp (- t ^ 4)` is not the characteristic function of any probability measure on `ℝ`. -/
theorem not_isCharFun_exp_neg_pow_four (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ t : ℝ, charFun μ t = Complex.exp (-(t : ℂ) ^ 4)) : False := by
  have hp : ∀ t : ℝ, charFun μ t
      = Complex.exp ((Polynomial.C (-1 : ℂ) * Polynomial.X ^ 4).eval (t : ℂ)) := by
    intro t
    rw [h t]
    congr 1
    simp
  have hdeg := charFun_eq_exp_polynomial_degree_le_two hp
  have : (Polynomial.C (-1 : ℂ) * Polynomial.X ^ 4).degree = 4 := by compute_degree!
  rw [this] at hdeg
  norm_num at hdeg

end Witness

end Marcinkiewicz

end StatLean.AsymptoticStatistics
