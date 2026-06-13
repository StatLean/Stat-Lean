import StatLean.Optimization.Convex.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# Subgradient API: the gradient is a subgradient

For a convex differentiable `f`, the gradient `∇f x` belongs to the
subdifferential `∂f x` (Lu, *Big Data Analysis* §10.2, "When `f` is
differentiable and convex, `∇f(x) ∈ ∂f(x)`"). Immediate from the first-order
convexity inequality.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- For convex differentiable `f`, the gradient is a subgradient:
`∇f x ∈ ∂f x` (Lu-BDA §10.2). -/
theorem gradient_mem_subdifferential
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f) (x : E) :
    gradient f x ∈ subdifferential f x := by
  rw [mem_subdifferential]
  intro y
  have h := inner_gradient_le_sub_of_convexOn hf hdiff x y
  linarith

end StatLean.Optimization
