import StatLean.HypothesisTesting.ForMathlib.BerryEsseen
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Foundations for Esseen's smoothing inequality: the sinc integral

Esseen's smoothing inequality — the analytic bridge from a characteristic-function estimate to
a Kolmogorov-distance estimate — is classically proved by convolving the distribution-function
difference with the **Fejér kernel**, whose Fourier transform is compactly supported. The very
first quantitative fact one needs is the normalisation of that kernel, and it reduces to the
**sinc integral**

`∫_ℝ (sin x / x)² dx = π`.

Mathlib v4.29.1 has neither this nor the Dirichlet integral `∫ sin x / x = π/2`. This file
supplies it, by Fourier inversion rather than by contour integration:

* `tent` — the triangle function `Λ(x) = max 0 (1 − |x|)`;
* `fourier_tent` — its Fourier transform is `(sin(πξ)/(πξ))²` (for `ξ ≠ 0`), computed by an
  explicit complex antiderivative on each of the two linear pieces;
* `integrable_sinc_sq` — `(sin x / x)²` is integrable, by the bound `min(1, x⁻²) ≤ 2/(1 + x²)`;
* `integral_sinc_sq` — `∫ (sin x / x)² = π`, obtained by evaluating the Fourier inversion
  formula for `Λ` at the origin: `∫ 𝓕 Λ = 𝓕⁻ (𝓕 Λ) 0 = Λ 0 = 1`.

Downstream this gives the total mass of the Fejér kernel, `∫ K_T = 1`, which is what Esseen's
smoothing argument consumes.
-/

open MeasureTheory intervalIntegral
open scoped FourierTransform Real Topology

namespace StatLean.HypothesisTesting

/-! ## The tent function -/

/-- The **tent (triangle) function** `Λ(x) = max 0 (1 − |x|)`, supported on `[-1, 1]`. -/
noncomputable def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_left _ _

lemma tent_zero : tent 0 = 1 := by simp [tent]

lemma tent_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  simp [tent, sub_nonpos.2 hx]

lemma tent_of_mem_Icc_zero_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : tent x = 1 - x := by
  have h : |x| = x := abs_of_nonneg hx.1
  simp only [tent, h]
  exact max_eq_right (by linarith [hx.2])

lemma tent_of_mem_Icc_neg_one_zero {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 0) :
    tent x = 1 + x := by
  have h : |x| = -x := abs_of_nonpos hx.2
  simp only [tent, h, sub_neg_eq_add]
  exact max_eq_right (by linarith [hx.1])

lemma continuous_tent : Continuous tent := by
  unfold tent; fun_prop

/-- `Λ` vanishes off `[-1, 1]`. -/
lemma tent_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : tent x = 0 := by
  refine tent_of_one_le_abs ?_
  rcases not_and_or.1 (fun h => hx ⟨h.1, h.2⟩) with h | h
  · rw [abs_of_nonpos (by linarith [not_le.1 h])]; linarith [not_le.1 h]
  · rw [abs_of_nonneg (by linarith [not_le.1 h])]; linarith [not_le.1 h]

/-! ## An explicit antiderivative for `(c + v) e^{a v}` -/

/-- The interval integral of `(c + v) e^{a v}` in the real variable `v`, computed from the
explicit antiderivative `((c + v)/a − 1/a²) e^{a v}`. -/
private lemma integral_linear_mul_cexp {a : ℂ} (ha : a ≠ 0) (c : ℂ) (p q : ℝ) :
    (∫ v in p..q, (c + (v : ℂ)) * Complex.exp (a * v)) =
      ((c + (q : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * q) -
        ((c + (p : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * p) := by
  have hderiv : ∀ v : ℝ, HasDerivAt
      (fun w : ℝ => ((c + (w : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * w))
      ((c + (v : ℂ)) * Complex.exp (a * v)) v := by
    intro v
    have hb : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 v := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := v)
    have h1 : HasDerivAt (fun w : ℝ => (c + (w : ℂ)) / a - 1 / a ^ 2) (1 / a) v := by
      simpa using ((hb.const_add c).div_const a).sub_const (1 / a ^ 2)
    have h2 : HasDerivAt (fun w : ℝ => Complex.exp (a * w))
        (Complex.exp (a * v) * a) v := by
      simpa using ((hb.const_mul a).cexp)
    have := h1.mul h2
    convert this using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun v : ℝ => (c + (v : ℂ)) * Complex.exp (a * v))
      MeasureTheory.volume p q := by
    apply Continuous.intervalIntegrable
    fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint

/-! ## The Fourier transform of the tent function -/

/-- The complexification of the tent function. -/
private noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

private lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

/-- **The Fourier transform of the triangle function is the squared sinc.**

With Mathlib's `e^{-2πi x ξ}` normalisation, `𝓕 Λ (ξ) = (sin(πξ)/(πξ))²` for `ξ ≠ 0`
(at `ξ = 0` the right-hand side is the junk value `0`, while `𝓕 Λ (0) = ∫ Λ = 1`). -/
theorem fourier_tentC {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 tentC ξ = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  obtain ⟨a, ha_def⟩ : ∃ a : ℂ, a = -2 * (π : ℂ) * (ξ : ℂ) * Complex.I := ⟨_, rfl⟩
  have ha : a ≠ 0 := by
    rw [ha_def]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · exact_mod_cast hπ
    · exact_mod_cast hξ
  -- Step 1: rewrite the Fourier integral in the form `∫ Λ(v) e^{a v}`.
  have hstep1 : 𝓕 tentC ξ = ∫ v : ℝ, tentC v * Complex.exp (a * v) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hexp : ((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I = a * (v : ℂ) := by
      rw [ha_def]; push_cast; ring
    dsimp only
    rw [smul_eq_mul, mul_comm, hexp]
  -- Step 2: the integrand is supported in `[-1, 1]`.
  have hsupp : ∀ v : ℝ, v ∉ Set.Icc (-1 : ℝ) 1 → tentC v * Complex.exp (a * v) = 0 := by
    intro v hv
    simp [tentC, tent_eq_zero_of_notMem hv]
  have hcont : Continuous fun v : ℝ => tentC v * Complex.exp (a * v) := by
    exact continuous_tentC.mul (by fun_prop)
  have hstep2 : (∫ v : ℝ, tentC v * Complex.exp (a * v))
      = ∫ v in (-1 : ℝ)..1, tentC v * Complex.exp (a * v) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  -- Step 3: split at the origin and evaluate each linear piece.
  have hsplit : (∫ v in (-1 : ℝ)..1, tentC v * Complex.exp (a * v))
      = (∫ v in (-1 : ℝ)..0, tentC v * Complex.exp (a * v)) +
        ∫ v in (0 : ℝ)..1, tentC v * Complex.exp (a * v) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hleft : (∫ v in (-1 : ℝ)..0, tentC v * Complex.exp (a * v))
      = ∫ v in (-1 : ℝ)..0, ((1 : ℂ) + (v : ℂ)) * Complex.exp (a * v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    simp [tentC, tent_of_mem_Icc_neg_one_zero hv]
  have hright : (∫ v in (0 : ℝ)..1, tentC v * Complex.exp (a * v))
      = ∫ v in (0 : ℝ)..1, -((((-1 : ℂ)) + (v : ℂ)) * Complex.exp (a * v)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rw [tentC, tent_of_mem_Icc_zero_one hv]
    push_cast
    ring
  rw [hstep1, hstep2, hsplit, hleft, hright, intervalIntegral.integral_neg,
    integral_linear_mul_cexp ha, integral_linear_mul_cexp ha]
  -- Step 4: the closed-form algebra.
  have he0 : Complex.exp (a * ((0 : ℝ) : ℂ)) = 1 := by
    norm_num
  have he1 : Complex.exp (a * ((1 : ℝ) : ℂ)) = Complex.exp a := by
    norm_num
  have hem1 : Complex.exp (a * ((-1 : ℝ) : ℂ)) = Complex.exp (-a) := by
    norm_num
  have hcos : Complex.exp a + Complex.exp (-a) = 2 * Complex.cos (2 * (π : ℂ) * (ξ : ℂ)) := by
    have h1 : a = (-(2 * (π : ℂ) * (ξ : ℂ))) * Complex.I := by rw [ha_def]; ring
    rw [h1, show -(-(2 * (π : ℂ) * (ξ : ℂ)) * Complex.I)
        = (2 * (π : ℂ) * (ξ : ℂ)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have ha2 : a ^ 2 = -(4 * (π : ℂ) ^ 2 * (ξ : ℂ) ^ 2) := by
    rw [ha_def]
    rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]
    ring
  have hsin : 2 - 2 * Complex.cos (2 * (π : ℂ) * (ξ : ℂ))
      = 4 * Complex.sin ((π : ℂ) * (ξ : ℂ)) ^ 2 := by
    have : (2 : ℂ) * (π : ℂ) * (ξ : ℂ) = 2 * ((π : ℂ) * (ξ : ℂ)) := by ring
    rw [this, Complex.cos_two_mul', Complex.cos_sq']
    ring
  have hπξ : ((π : ℂ) * (ξ : ℂ)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast hπ
    · exact_mod_cast hξ
  have hsum : Complex.exp a + Complex.exp (-a) - 2
      = -(4 * Complex.sin ((π : ℂ) * (ξ : ℂ)) ^ 2) := by
    rw [hcos]
    linear_combination -hsin
  have hfinal : (Complex.exp a + Complex.exp (-a) - 2) / a ^ 2
      = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
    rw [hsum, ha2]
    push_cast
    field_simp
  rw [he0, he1, hem1, ← hfinal]
  field_simp
  push_cast
  ring

/-! ## Integrability and the value of the sinc integral -/

/-- The elementary bound `(sin x / x)² ≤ 2/(1 + x²)`, from `sin²x ≤ min (1, x²)`. -/
private lemma sq_sin_div_le (x : ℝ) : (Real.sin x / x) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have h2 : Real.sin x ^ 2 ≤ x ^ 2 := Real.sin_sq_le_sq
  rw [div_pow, ← div_eq_mul_inv, div_le_div_iff₀ hx2 hpos]
  rcases le_or_gt (x ^ 2) 1 with h | h
  · nlinarith [sq_nonneg (Real.sin x)]
  · nlinarith [sq_nonneg (Real.sin x)]

/-- **The squared sinc function is integrable on the line.** -/
theorem integrable_sin_div_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) := by
  refine Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2)
    ((Real.continuous_sin.measurable.div measurable_id).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_sin_div_le x

/-- **The sinc integral.** `∫_ℝ (sin x / x)² dx = π`.

The proof evaluates the Fourier inversion formula for the triangle function `Λ` at the
origin: `𝓕 Λ` is the squared sinc `(sin(πξ)/(πξ))²` (`fourier_tentC`), which is integrable,
so `∫ 𝓕 Λ = 𝓕⁻ (𝓕 Λ) 0 = Λ 0 = 1`; rescaling by `π` gives the stated value. -/
theorem integral_sin_div_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  -- the `π`-rescaled squared sinc is integrable, and equals `𝓕 Λ` off the origin
  have hscaled : Integrable (fun ξ : ℝ => (Real.sin (π * ξ) / (π * ξ)) ^ 2) :=
    MeasureTheory.Integrable.comp_mul_left' integrable_sin_div_sq hπ
  have hae : 𝓕 tentC =ᵐ[volume] fun ξ : ℝ => (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with ξ hξ
    exact fourier_tentC (by simpa using hξ)
  have hFint : Integrable (𝓕 tentC) := hscaled.ofReal.congr hae.symm
  -- Fourier inversion at the origin
  have hcs : HasCompactSupport tentC :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [tentC, tent_eq_zero_of_notMem hx]
  have htent : Integrable tentC := continuous_tentC.integrable_of_hasCompactSupport hcs
  have hinv : 𝓕⁻ (𝓕 tentC) (0 : ℝ) = tentC 0 :=
    htent.fourierInv_fourier_eq hFint continuous_tentC.continuousAt
  have h0 : 𝓕⁻ (𝓕 tentC) (0 : ℝ) = ∫ ξ : ℝ, 𝓕 tentC ξ := by
    rw [Real.fourierInv_eq]
    simp
  -- hence the rescaled integral is `1`
  have hone : (∫ ξ : ℝ, (Real.sin (π * ξ) / (π * ξ)) ^ 2) = 1 := by
    have h : (∫ ξ : ℝ, (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)) = 1 := by
      rw [← integral_congr_ae hae, ← h0, hinv, tentC, tent_zero]
      norm_num
    exact_mod_cast h
  -- undo the rescaling
  have hchange := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => (Real.sin u / u) ^ 2) π
  rw [hone, smul_eq_mul, abs_of_pos (inv_pos.2 Real.pi_pos)] at hchange
  have h2 := congrArg (fun z : ℝ => π * z) hchange.symm
  simp only [← mul_assoc, mul_inv_cancel₀ hπ, one_mul, mul_one] at h2
  exact h2

/-! ## The Fejér kernel: total mass and Fourier transform -/

/-- **The Fejér kernel is a probability density**: `∫ K_T = 1` for `T > 0`. This is the
normalisation that Esseen's smoothing argument consumes, and it is exactly the sinc integral
after the substitution `u = T x / 2`. -/
theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ x : ℝ, fejerKernel T x = 1 := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : ∀ x : ℝ,
      fejerKernel T x = (T / (2 * π)) * (Real.sin (T / 2 * x) / (T / 2 * x)) ^ 2 := by
    intro x
    unfold fejerKernel
    rw [show T * x / 2 = T / 2 * x from by ring]
  have hg : (∫ x : ℝ, (Real.sin (T / 2 * x) / (T / 2 * x)) ^ 2)
      = |(T / 2)⁻¹| • ∫ y : ℝ, (Real.sin y / y) ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => (Real.sin u / u) ^ 2) (T / 2)
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, hg, integral_sin_div_sq, smul_eq_mul,
    abs_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < T / 2))]
  field_simp

/-- The tent function is even. -/
lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp [tent]

/-- The complexified squared sinc `ξ ↦ (sin(πξ)/(πξ))²`, i.e. `𝓕 Λ` up to the null set `{0}`. -/
private noncomputable def sqSincC (ξ : ℝ) : ℂ := (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)

private lemma fourier_tentC_ae : 𝓕 tentC =ᵐ[volume] sqSincC := by
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with ξ hξ
  exact fourier_tentC (by simpa using hξ)

private lemma integrable_sqSincC : Integrable sqSincC :=
  (MeasureTheory.Integrable.comp_mul_left' integrable_sin_div_sq Real.pi_ne_zero).ofReal

/-- **The Fourier transform of the squared sinc is the triangle function.**

This is the second half of the classical Fejér/triangle Fourier pair, and it is the fact that
makes Esseen's smoothing work: the transform is **compactly supported**, in `[-1, 1]`. It is
obtained from `fourier_tentC` by Fourier inversion together with the evenness of `Λ`. -/
theorem fourier_sqSincC : 𝓕 sqSincC = tentC := by
  have hcs : HasCompactSupport tentC :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [tentC, tent_eq_zero_of_notMem hx]
  have htent : Integrable tentC := continuous_tentC.integrable_of_hasCompactSupport hcs
  have hFint : Integrable (𝓕 tentC) := integrable_sqSincC.congr fourier_tentC_ae.symm
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    continuous_tentC.fourierInv_fourier_eq htent hFint
  funext x
  have h1 : 𝓕 sqSincC x = 𝓕 (𝓕 tentC) x :=
    (Real.fourier_congr_ae fourier_tentC_ae x).symm
  have h2 : 𝓕 (𝓕 tentC) x = 𝓕⁻ (𝓕 tentC) (-x) := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [h1, h2, hinv]
  simp [tentC, tent_neg]

/-! ## The smoothing (Parseval) identity against a finite measure -/

/-- **Parseval's identity against a finite measure.** For every integrable `g : ℝ → ℂ`,

`∫ 𝓕 g dP = ∫ charFun P (−2πξ) · g(ξ) dξ`.

This is the analytic core of the smoothing step: it converts an integral of a *smooth test
function* against `P` into an integral of the *characteristic function* of `P` against the
transform. Applied to `P − Q` with a `g` whose transform is compactly supported — such as the
triangle function of `fourier_sqSincC`, rescaled — it bounds a smoothed functional of the
difference using only the characteristic functions on a compact frequency window, which is
exactly what Esseen's argument needs. -/
theorem integral_fourier_measure {P : Measure ℝ} [IsFiniteMeasure P] {g : ℝ → ℂ}
    (hg : Integrable g) :
    ∫ x : ℝ, 𝓕 g x ∂P = ∫ ξ : ℝ, charFun P (-(2 * π * ξ)) * g ξ := by
  have hL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 := continuous_inner
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    exact real_inner_comm x y
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := P) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun _ : ℝ => (1 : ℂ)) (g := g)
    Real.continuous_fourierChar hL (integrable_const 1) hg
  rw [hflip] at key
  have hchar : ∀ ξ : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar P (innerₗ ℝ) (fun _ : ℝ => (1 : ℂ)) ξ
        = charFun P (-(2 * π * ξ)) := by
    intro ξ
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul, charFun_apply_real]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hin : ((innerₗ ℝ) v) ξ = v * ξ := by
      simp only [innerₗ_apply_apply]
      change ξ * v = v * ξ
      ring
    dsimp only
    rw [hin, smul_eq_mul, mul_one]
    congr 1
    push_cast
    ring
  have hfour : ∀ x : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x = 𝓕 g x :=
    fun _ => rfl
  simp only [hchar, hfour, smul_eq_mul, one_mul] at key
  exact key.symm

end StatLean.HypothesisTesting
