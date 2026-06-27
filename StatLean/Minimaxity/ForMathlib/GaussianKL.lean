import Mathlib.Probability.Distributions.Gaussian.Basic
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

/-- **KL divergence between equal-variance real Gaussians** (Wainwright Exercise 15.13, equal-
covariance case): `D(𝒩(m₁, σ²) ‖ 𝒩(m₂, σ²)) = (m₁ − m₂)² / (2σ²)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.13. -/
theorem klDiv_gaussianReal (m₁ m₂ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v)
      = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * (v : ℝ))) := by
  sorry

end StatLean.Minimaxity
