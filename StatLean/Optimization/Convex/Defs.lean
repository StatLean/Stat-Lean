import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Subgradient and subdifferential

Concept-layer definitions for the `Optimization` area: the subgradient of a
function `f : E → ℝ` at a point and the subdifferential set `∂f(x)`
(Lu, *Big Data Analysis* §10.2, Definition "Subgradient").

The book states the definition on a convex domain `𝒳`; we formalize the
unconstrained case `𝒳 = E` (the whole inner product space), which is what the
targeted results (`prop:local-global`, the proximal pillar lemma) require.

Convexity of sets/functions is reused directly from Mathlib (`Convex`,
`ConvexOn`); this file only adds the subgradient notion, which Mathlib lacks for
multivariate functions.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `IsSubgradient f x g`: `g` is a subgradient of `f : E → ℝ` at `x`, i.e. the
supporting-hyperplane inequality `f y - f x ≥ ⟪g, y - x⟫` holds for every `y`
(Lu-BDA §10.2, "Subgradient", specialized to the unconstrained domain `𝒳 = E`).
For differentiable convex `f` the gradient `∇f x` is the canonical subgradient. -/
def IsSubgradient (f : E → ℝ) (x g : E) : Prop :=
  ∀ y, ⟪g, y - x⟫_ℝ ≤ f y - f x

/-- The subdifferential `∂f(x)`: the set of all subgradients of `f` at `x`
(Lu-BDA §10.2). May be empty for nonconvex `f`; for convex `f` it is nonempty. -/
def subdifferential (f : E → ℝ) (x : E) : Set E :=
  {g | IsSubgradient f x g}

@[simp] theorem mem_subdifferential {f : E → ℝ} {x g : E} :
    g ∈ subdifferential f x ↔ IsSubgradient f x g := Iff.rfl

end StatLean.Optimization
