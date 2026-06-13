import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
# Gradient at an extremum

Theorem-agnostic brick (`ForMathlib` layer): at an interior local (hence at a
global) minimizer of a differentiable function, the gradient vanishes.

This bridges Mathlib's Fermat-type `IsLocalMin.fderiv_eq_zero` to the
Riesz-representation `gradient`, giving the `∇f(x*) = 0` fact used in the
unconstrained gradient-descent analysis (Lu, *Big Data Analysis* §11.1).
-/

namespace StatLean.Optimization

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- At a global minimizer of a differentiable function, the gradient is zero. -/
theorem gradient_eq_zero_of_forall_le
    {f : E → ℝ} (hdiff : Differentiable ℝ f) {x : E} (hmin : ∀ y, f x ≤ f y) :
    gradient f x = 0 := by
  sorry

end StatLean.Optimization
