import StatLean.Minimaxity.Fano.LocalPacking
import StatLean.Minimaxity.ForMathlib.GaussianKL
import StatLean.Minimaxity.ForMathlib.Packing.SparsePacking
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Example: minimax risks for linear regression (Wainwright Examples 15.14, 15.16)

For the Gaussian linear model `y = Xθ* + w`, `w ∼ 𝒩(0, σ²Iₙ)`, with the prediction semimetric
`ρ_X(θ, θ') = ‖X(θ − θ')‖₂/√n`, the local-packing / Fano method gives
```
inf_θ̂ sup_θ 𝔼[(1/n)‖X(θ̂ − θ)‖₂²] ≥ (σ²/128) · rank(X)/n          (Example 15.14),
```
and, restricting to `s`-sparse regression vectors,
```
M(𝕊ᵈ(s); ‖·‖₂) ≳ (σ²/γ²) · (s log(d/s))/n                        (Example 15.16).
```

We realize the prediction semimetric as the Euclidean `edist` on the prediction space by taking
`g θ = (1/√n)·(A θ)` where `A` is the design map, so `ρ(g θ, g θ') = ρ_X(θ, θ')`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.14.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for fixed-design linear regression** (Wainwright Example 15.14): for the Gaussian
model with design map `A : ℝᵈ → ℝⁿ` and noise variance `v`, the minimax risk in the prediction
(semi)norm `ρ_X(θ,θ') = ‖A(θ−θ')‖/√n` is at least `(v/128)·rank(A)/n`, where `g θ = A θ/√n` realizes
`ρ_X` as the Euclidean distance.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.14. -/
theorem linear_regression_minimax_rate {n d : ℕ} (hn : 1 ≤ n) (v : ℝ≥0) (hv : v ≠ 0) (r : ℕ)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n))
    (P : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    -- USER-INPUT: `g θ = A θ/√n` is the normalized prediction map; Wainwright §15.3.3, Ex 15.14.
    (hg : ∀ θ, g θ = (Real.sqrt n)⁻¹ • A θ)
    -- USER-INPUT: `y ∼ 𝒩(Aθ, v Iₙ)` (fixed-design Gaussian model); Wainwright §15.3.3, Ex 15.14.
    (hP : ∀ θ, P θ = multivariateGaussian (A θ) ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    -- USER-INPUT: `r = rank(A)`; Wainwright §15.3.3, Ex 15.14.
    (hr : r = Module.finrank ℝ (LinearMap.range A)) :
    ENNReal.ofReal ((v : ℝ) * r / (128 * n)) ≤ minimaxRiskDist (· ^ 2) g P := by
  sorry

end StatLean.Minimaxity
