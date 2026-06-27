import StatLean.Minimaxity.LeCam.TwoPoint
import StatLean.Minimaxity.ForMathlib.GaussianKL
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

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

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
  sorry

end StatLean.Minimaxity
