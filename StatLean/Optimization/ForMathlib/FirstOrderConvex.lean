import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

/-!
# First-order characterization of convexity (gradient inequality)

Theorem-agnostic brick (`ForMathlib` layer): a convex differentiable function
lies above each of its tangents,
`f x + ⟪∇f x, y - x⟫ ≤ f y`.

This is the differentiable specialization of the subgradient inequality (the
book derives it in Lu, *Big Data Analysis* §10.2 by taking `γ → 0` in the
convexity inequality). Mathlib has the 1-D `deriv` version but not the
inner-product-space gradient form; we prove it here for reuse across the
gradient-descent, Frank–Wolfe, and proximal analyses.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Gradient inequality for convex differentiable functions:
`f x + ⟪∇f x, y - x⟫ ≤ f y` for all `x y` (Lu-BDA §10.2). -/
theorem inner_gradient_le_sub_of_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  sorry

end StatLean.Optimization
