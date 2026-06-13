import StatLean.Optimization.Smoothness.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# Convergence of the Frank–Wolfe algorithm (Theorem 11.2)

Lu, *Big Data Analysis* §11.2, Theorem `thm:fw-rate`: for a convex `L`-smooth
`f` minimized over a convex set `X` of squared diameter `≤ D`, the Frank–Wolfe
iterates with step `η_t = 2/(t+2)` satisfy `f(x_t) - f(x*) ≤ 2 L D / (t+2)`.

The linear-minimization oracle is a hypothesis (`hlmo`): each `y_t ∈ X`
minimizes `z ↦ ⟪∇f(x_t), z⟫` over `X` — the genuine external input describing
the per-step subproblem, avoiding any compactness / argmin-existence machinery.
The diameter enters only through the per-step bound `‖y_t - x_t‖² ≤ D`
(`hdiam`). The proof: smoothness + the oracle + convexity give the recursion
`Δ_{t+1} ≤ (1 - η_t) Δ_t + (L/2) η_t² D`, closed by induction with
`η_t = 2/(t+2)`.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lu-BDA Thm 11.2 (Frank–Wolfe convergence rate). Convex `L`-smooth `f`,
convex feasible set `X` with squared diameter `≤ D`, linear-minimization oracle
`hlmo`, step `η_t = 2/(t+2)`: `f(x_t) - f(x*) ≤ 2 L D / (t+2)`. -/
theorem frankWolfe_rate
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    {X : Set E} (hX : Convex ℝ X) {D : ℝ}
    (x y : ℕ → E)
    (hxX : ∀ t, x t ∈ X)
    (hlmo : ∀ t, y t ∈ X ∧ ∀ z ∈ X, ⟪gradient f (x t), y t⟫_ℝ ≤ ⟪gradient f (x t), z⟫_ℝ)
    (hdiam : ∀ t, ‖y t - x t‖ ^ 2 ≤ D)
    (hrec : ∀ t, x (t + 1) = x t + (2 / ((t : ℝ) + 2)) • (y t - x t))
    {xstar : E} (hxsX : xstar ∈ X) (hmin : ∀ z ∈ X, f xstar ≤ f z)
    (t : ℕ) :
    f (x t) - f xstar ≤ 2 * L * D / ((t : ℝ) + 2) := by
  sorry

end StatLean.Optimization
