import StatLean.Optimization.Prox.Pillar
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Convergence of accelerated proximal gradient descent (Theorem 12.2)

Lu, *Big Data Analysis* §12.2, Theorem `thm:cvg-aprox`: with Nesterov momentum,
the accelerated proximal-gradient iterates achieve the faster `O(1/t²)` rate
`F(x_t) - F(x*) ≤ 2L‖x_0 - x*‖² / (t+1)²`.

Algorithm (with `x_0 = y_0`, `λ_0 = 1`, `λ_{t+1} = (1 + √(1 + 4λ_t²))/2`):
* `x_{t+1} = prox_{(1/L)h}(y_t - (1/L)∇f(y_t))`;
* `y_{t+1} = x_{t+1} + ((λ_t - 1)/λ_{t+1})(x_{t+1} - x_t)`.

The proof is not monotone in `F`; it uses the pillar inequality (Lemma 12.1)
together with a Lyapunov energy `L_t = ‖u_t‖² + (2/L)λ_{t-1}²(F(x_t) - F(x*))`
(Lemma 12.2 below) shown to be non-increasing, plus the Nesterov-sequence bound
`λ_t ≥ (t+2)/2` (`nesterov_lambda_lower`).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Nesterov extrapolation sequence `λ_0 = 1`,
`λ_{t+1} = (1 + √(1 + 4λ_t²))/2` satisfies `λ_t ≥ (t+2)/2` (Lu-BDA §12.2). -/
theorem nesterov_lambda_lower
    (lam : ℕ → ℝ) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (t : ℕ) :
    ((t : ℝ) + 2) / 2 ≤ lam t := by
  sorry

/-- Lu-BDA Thm 12.2 (accelerated proximal-gradient convergence rate). `f` convex
`L`-smooth (`0 < L`), `h` convex, `F = f + h`, step `1/L`, Nesterov momentum:
`F(x_t) - F(x*) ≤ 2L‖x_0 - x*‖² / (t+1)²`. -/
theorem acceleratedProximalGradient_rate
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    (x y : ℕ → E) (lam : ℕ → ℝ)
    (hxy0 : y 0 = x 0)
    (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (hxrec : ∀ t, IsProxMinimizer ((1 / L) • h)
        (y t - (1 / L) • gradient f (y t)) (x (t + 1)))
    (hyrec : ∀ t, y (t + 1) = x (t + 1) + ((lam t - 1) / lam (t + 1)) • (x (t + 1) - x t))
    {xstar : E} (hmin : ∀ z, f xstar + h xstar ≤ f z + h z)
    (t : ℕ) :
    (f (x t) + h (x t)) - (f xstar + h xstar)
      ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2 := by
  sorry

end StatLean.Optimization
