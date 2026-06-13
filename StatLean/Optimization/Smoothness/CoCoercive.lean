import StatLean.Optimization.Smoothness.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# Co-coercivity of the gradient (Lemma 11.1)

For a convex `L`-smooth function, the gradient satisfies the co-coercivity
inequality (Lu, *Big Data Analysis* §11.1, Lemma 11.1):
`f x - f y ≤ ⟪∇f x, x - y⟫ - (1/(2L)) ‖∇f x - ∇f y‖²`.

The book states it for `L`-smooth `f`, but its proof (evaluate the smoothness
upper bound at `z = y - (1/L)(∇f y - ∇f x)` and add the convexity inequality)
also uses convexity. We therefore state both hypotheses — a deliberate
hypothesis correction over the book text.

This is the key lemma behind the monotone-distance step of the gradient-descent
rate (Theorem 11.1).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Co-coercivity (Lu-BDA Lemma 11.1). For convex `L`-smooth `f` with `0 < L`:
`f x - f y ≤ ⟪∇f x, x - y⟫ - (1/(2L)) ‖∇f x - ∇f y‖²`. -/
theorem cocoercive
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (x y : E) :
    f x - f y ≤ ⟪gradient f x, x - y⟫_ℝ
      - (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2 := by
  sorry

/-- Monotonicity of the gradient (immediate corollary of co-coercivity):
`(1/(2L)) ‖∇f x - ∇f y‖² ≤ ⟪∇f x - ∇f y, x - y⟫` (Lu-BDA §11.1). -/
theorem inner_gradient_sub_nonneg
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (x y : E) :
    (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2
      ≤ ⟪gradient f x - gradient f y, x - y⟫_ℝ := by
  sorry

end StatLean.Optimization
