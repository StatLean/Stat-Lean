import StatLean.Optimization.Prox.Defs
import StatLean.Optimization.Smoothness.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# The pillar inequality (Lemma 12.1)

The fundamental inequality behind both proximal-gradient convergence theorems
(Lu, *Big Data Analysis* §12.1, Lemma `lm:pillar`): for convex `L`-smooth `f`,
convex `h`, `F = f + h`, and a single proximal step
`y⁺ = prox_{(1/L)h}(y - (1/L)∇f y)`,
`F y⁺ - F x ≤ (L/2)‖x - y‖² - (L/2)‖x - y⁺‖²` for every `x`.

The proof combines:
* L-smoothness of `f` at `y⁺` vs `y`;
* convexity (gradient inequality) of `f` at `y` vs `x`;
* the variational inequality of the prox step (`prox_variational_inequality`
  below), which plays the role of the subgradient optimality
  `0 ∈ ∇f y + L(y⁺ - y) + ∂h(y⁺)` in the book, but is derived purely from
  convexity of `h` and the minimization property — no subgradient existence
  needed.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Variational inequality of the proximal minimizer. If `z = prox_h(x)` and `h`
is convex, then `⟪x - z, w - z⟫ ≤ h w - h z` for all `w`. This is the
first-order optimality of the prox subproblem, obtained from a convex
perturbation `proxObj h x z ≤ proxObj h x (z + t(w - z))` letting `t → 0⁺`. -/
theorem prox_variational_inequality
    {h : E → ℝ} (hh : ConvexOn ℝ Set.univ h) {x z : E}
    (hz : IsProxMinimizer h x z) (w : E) :
    ⟪x - z, w - z⟫_ℝ ≤ h w - h z := by
  sorry

/-- Pillar inequality (Lu-BDA Lemma 12.1). For convex `L`-smooth `f` (`0 < L`),
convex `h`, and the prox step `y⁺ = prox_{(1/L)h}(y - (1/L)∇f y)`,
`(f y⁺ + h y⁺) - (f x + h x) ≤ (L/2)‖x - y‖² - (L/2)‖x - y⁺‖²`. -/
theorem pillar
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    {x y yplus : E}
    (hyplus : IsProxMinimizer ((1 / L) • h) (y - (1 / L) • gradient f y) yplus) :
    (f yplus + h yplus) - (f x + h x)
      ≤ (L / 2) * ‖x - y‖ ^ 2 - (L / 2) * ‖x - yplus‖ ^ 2 := by
  sorry

end StatLean.Optimization
