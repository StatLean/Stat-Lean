import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# L-smoothness

Concept-layer definition for the `Optimization` area: `L`-smoothness of a
function `f : E → ℝ` (Lu, *Big Data Analysis* §11, Definition `def:lsmooth`,
"`L`-smooth").

The book gives the quadratic upper-bound form
`f y ≤ f x + ⟪∇f x, y - x⟫ + (L/2)‖x - y‖²`
as the primary definition and notes that, for `C¹` functions, it is equivalent to
the gradient being `L`-Lipschitz. We take the upper bound itself as the
definition — it is exactly the inequality consumed by the descent analyses
(gradient descent, Frank–Wolfe, proximal gradient), so no separate "descent
lemma" is needed.

Here `gradient f x` is Mathlib's Riesz-representation gradient (`= 0` where `f`
is not differentiable). Downstream theorems carry differentiability of `f`
explicitly when they need `gradient f x` to be the genuine derivative.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `IsLSmooth f L`: the function `f : E → ℝ` is `L`-smooth, i.e. it lies below
the quadratic model around every point,
`f y ≤ f x + ⟪∇f x, y - x⟫ + (L/2)‖x - y‖²` for all `x y` (Lu-BDA §11,
`def:lsmooth`). `gradient f x` is the Riesz gradient. -/
def IsLSmooth (f : E → ℝ) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + (L / 2) * ‖x - y‖ ^ 2

end StatLean.Optimization
