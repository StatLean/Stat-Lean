import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap

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
  -- Restrict `f` to the line through `x` and `y` via `L = lineMap x y`.
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hLdef
  have hL0 : (L : ℝ → E) 0 = x := by rw [hLdef]; exact AffineMap.lineMap_apply_zero x y
  have hL1 : (L : ℝ → E) 1 = y := by rw [hLdef]; exact AffineMap.lineMap_apply_one x y
  -- `f ∘ L` is convex on `Set.univ` (preimage of univ under L is univ).
  have hφconv : ConvexOn ℝ Set.univ (f ∘ ⇑L) := by
    have h : ConvexOn ℝ (⇑L ⁻¹' Set.univ) (f ∘ ⇑L) := ConvexOn.comp_affineMap L hf
    simpa using h
  -- Chain rule: derivative of `L` is `y - x`; derivative of `f ∘ L` at `0` is
  -- `(fderiv ℝ f x) (y - x) = ⟪∇f x, y - x⟫`.
  have hLderiv : HasDerivAt (⇑L : ℝ → E) (y - x) 0 := by
    rw [hLdef]; exact AffineMap.hasDerivAt_lineMap
  have hfderiv : HasFDerivAt f (fderiv ℝ f x) ((L : ℝ → E) 0) := by
    rw [hL0]; exact (hdiff x).hasFDerivAt
  have hφderiv : HasDerivAt (f ∘ ⇑L) ((fderiv ℝ f x) (y - x)) 0 :=
    hfderiv.comp_hasDerivAt 0 hLderiv
  -- Apply the 1-D first-order convexity inequality: `f' ≤ slope` for `0 < 1`.
  have hslope : (fderiv ℝ f x) (y - x) ≤ slope (f ∘ ⇑L) 0 1 :=
    hφconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφderiv
  have hsl : slope (f ∘ ⇑L) 0 1 = f y - f x := by
    rw [slope_def_field]
    show ((f ∘ ⇑L) 1 - (f ∘ ⇑L) 0) / (1 - 0) = f y - f x
    rw [Function.comp_apply, Function.comp_apply, hL0, hL1]
    norm_num
  rw [hsl] at hslope
  -- Riesz bridge: `⟪∇f x, v⟫ = fderiv f x v`.
  have hinner : ⟪gradient f x, y - x⟫_ℝ = (fderiv ℝ f x) (y - x) :=
    inner_gradient_left (hdiff x)
  linarith

end StatLean.Optimization
