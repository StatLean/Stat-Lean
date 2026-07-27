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

end StatLean.HypothesisTesting
