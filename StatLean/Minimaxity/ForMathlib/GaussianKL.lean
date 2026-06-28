import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback–Leibler divergence between Gaussians (Wainwright Exercise 15.13)

The explicit KL divergence between Gaussian distributions, used in the Gaussian-location and
linear-regression minimax examples (15.4, 15.13, 15.14, 15.16). For equal variance the formula is
```
D(𝒩(m₁, σ²) ‖ 𝒩(m₂, σ²)) = (m₁ − m₂)² / (2σ²)        (Exercise 15.13, equal-covariance case),
```
the mean-shift term of the general multivariate formula
`D(𝒩(μ₁,Σ)‖𝒩(μ₂,Σ)) = ½⟨μ₁−μ₂, Σ⁻¹(μ₁−μ₂)⟩`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.13.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- Logarithm of the Gaussian density splits into the (mean-independent) normalising constant and
the quadratic exponent: `log p_{m,v}(x) = -log √(2πv) − (x−m)²/(2v)`. -/
private lemma log_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = - Real.log (Real.sqrt (2 * Real.pi * v)) - (x - m) ^ 2 / (2 * (v : ℝ)) := by
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hsqrt : Real.sqrt (2 * Real.pi * v) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi * v := by positivity
    exact (Real.sqrt_pos.mpr this).ne'
  simp only [gaussianPDFReal]
  rw [Real.log_mul (inv_ne_zero hsqrt) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

/-- **KL divergence between equal-variance real Gaussians** (Wainwright Exercise 15.13, equal-
covariance case): `D(𝒩(m₁, σ²) ‖ 𝒩(m₂, σ²)) = (m₁ − m₂)² / (2σ²)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.13. -/
theorem klDiv_gaussianReal (m₁ m₂ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v)
      = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * (v : ℝ))) := by
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hvne : (v : ℝ) ≠ 0 := hv'.ne'
  -- absolute continuity `𝒩(m₁,v) ≪ 𝒩(m₂,v)` via the common dominating Lebesgue measure
  have hac : gaussianReal m₁ v ≪ gaussianReal m₂ v :=
    (gaussianReal_absolutelyContinuous m₁ hv).trans (gaussianReal_absolutelyContinuous' m₂ hv)
  -- the affine surrogate for the log-likelihood ratio
  set F : ℝ → ℝ := fun x => ((x - m₂) ^ 2 - (x - m₁) ^ 2) / (2 * (v : ℝ)) with hF_def
  -- `llr =ᵐ[𝒩(m₁,v)] F`
  have hllr : llr (gaussianReal m₁ v) (gaussianReal m₂ v) =ᵐ[gaussianReal m₁ v] F := by
    -- rnDeriv against Lebesgue
    have hrn_vol : (gaussianReal m₁ v).rnDeriv (gaussianReal m₂ v) =ᵐ[volume]
        fun x => (gaussianPDF m₂ v x)⁻¹ * gaussianPDF m₁ v x := by
      have h1 := Measure.rnDeriv_withDensity_right (gaussianReal m₁ v) volume
        (f := gaussianPDF m₂ v) (measurable_gaussianPDF m₂ v).aemeasurable
        (ae_of_all _ fun x => (gaussianPDF_pos m₂ hv x).ne')
        (ae_of_all _ fun _ => gaussianPDF_ne_top)
      rw [← gaussianReal_of_var_ne_zero m₂ hv] at h1
      filter_upwards [h1, rnDeriv_gaussianReal m₁ v] with x hx hx1
      rw [hx, hx1]
    have hrn : (gaussianReal m₁ v).rnDeriv (gaussianReal m₂ v) =ᵐ[gaussianReal m₁ v]
        fun x => (gaussianPDF m₂ v x)⁻¹ * gaussianPDF m₁ v x :=
      (gaussianReal_absolutelyContinuous m₁ hv).ae_eq hrn_vol
    filter_upwards [hrn] with x hx
    simp only [llr]
    rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
      Real.log_mul (inv_ne_zero (gaussianPDFReal_pos m₂ v x hv).ne')
        (gaussianPDFReal_pos m₁ v x hv).ne', Real.log_inv,
      log_gaussianPDFReal m₁ v hv, log_gaussianPDFReal m₂ v hv, hF_def]
    ring
  -- `F` is integrable against `𝒩(m₁,v)` (it is affine, the quadratic term cancels)
  have hFint : Integrable F (gaussianReal m₁ v) := by
    have key : F = fun x => ((m₁ - m₂) / (v : ℝ)) * x + (m₂ ^ 2 - m₁ ^ 2) / (2 * (v : ℝ)) := by
      funext x; rw [hF_def]; field_simp; ring
    rw [key]
    exact (ProbabilityTheory.IsGaussian.integrable_fun_id.const_mul _).add (integrable_const _)
  have hint : Integrable (llr (gaussianReal m₁ v) (gaussianReal m₂ v)) (gaussianReal m₁ v) :=
    hFint.congr hllr.symm
  -- evaluate `∫ F d𝒩(m₁,v)`
  have hFval : ∫ x, F x ∂(gaussianReal m₁ v) = (m₁ - m₂) ^ 2 / (2 * (v : ℝ)) := by
    have key : F = fun x => ((m₁ - m₂) / (v : ℝ)) * x + (m₂ ^ 2 - m₁ ^ 2) / (2 * (v : ℝ)) := by
      funext x; rw [hF_def]; field_simp; ring
    rw [key, integral_add (ProbabilityTheory.IsGaussian.integrable_fun_id.const_mul _)
      (integrable_const _), integral_const_mul, integral_id_gaussianReal, integral_const,
      probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr, probReal_univ, probReal_univ,
    add_sub_cancel_right, hFval]

end StatLean.Minimaxity
