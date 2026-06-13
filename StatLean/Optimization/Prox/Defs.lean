import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Proximal operator

Concept-layer definitions for the `Optimization` area: the proximal objective
and the predicate characterizing a proximal step (Lu, *Big Data Analysis*
§12.1, Definition "proximal operator").

The book defines `prox_h(x) = argmin_z { ½‖z - x‖² + h(z) }`. Rather than
construct the minimizer (which would require properness / lower
semicontinuity / coercivity of `h` to guarantee existence), we expose the
minimization *property* as a predicate `IsProxMinimizer`. The proximal
algorithms then take "this iterate is a prox step of the previous point" as an
oracle hypothesis — the legitimate external input describing what the algorithm
computes, mirroring the book's algorithm definition.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The proximal objective `proxObj h x z = ½‖z - x‖² + h z`, whose minimizer
over `z` defines `prox_h(x)` (Lu-BDA §12.1). `noncomputable` as it uses real
division. -/
noncomputable def proxObj (h : E → ℝ) (x z : E) : ℝ := (1 / 2) * ‖z - x‖ ^ 2 + h z

/-- `IsProxMinimizer h x z`: `z` attains the minimum of `proxObj h x`, i.e.
`z = prox_h(x)` (Lu-BDA §12.1). Characterizing the prox point by its
minimization property avoids committing to an existence theorem for the
minimizer. -/
def IsProxMinimizer (h : E → ℝ) (x z : E) : Prop :=
  ∀ w, proxObj h x z ≤ proxObj h x w

end StatLean.Optimization
