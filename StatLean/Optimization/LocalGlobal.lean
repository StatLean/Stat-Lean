import StatLean.Optimization.Convex.Defs
import Mathlib.Topology.Order.LocalExtr

/-!
# Local minima are global minima (Proposition 10.1)

Lu, *Big Data Analysis* §10.2, Proposition `prop:local-global`:

* for a convex function, every local minimizer is a global minimizer;
* `x*` is a global minimizer iff `0 ∈ ∂f(x*)` (the first-order optimality
  condition for unconstrained problems).

The second statement is essentially definitional via `IsSubgradient`
(`0 ∈ ∂f x*` unfolds to `∀ y, 0 ≤ f y - f x*`); the first uses convexity.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lu-BDA Prop 10.1 (first-order optimality, unconstrained): `x*` is a global
minimizer of `f` iff `0 ∈ ∂f(x*)`. -/
theorem isGlobalMin_iff_zero_mem_subdifferential (f : E → ℝ) (xstar : E) :
    (∀ y, f xstar ≤ f y) ↔ (0 : E) ∈ subdifferential f xstar := by
  sorry

/-- Lu-BDA Prop 10.1 (local minima are global minima): for convex `f`, any local
minimizer is a global minimizer. -/
theorem forall_le_of_isLocalMin
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {xstar : E}
    (hloc : IsLocalMin f xstar) (y : E) :
    f xstar ≤ f y := by
  sorry

end StatLean.Optimization
