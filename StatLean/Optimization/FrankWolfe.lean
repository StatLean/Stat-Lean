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

Architecture: `frankWolfe_step` proves the one-step recursion; `frankWolfe_rate`
then closes by `Nat.le_induction` for `t ≥ 1`, with base case `t = 1` coming from
one FW step at `t = 0` (`η_0 = 1 ⇒ Δ_1 ≤ (L/2)D ≤ 2LD/3`). The theorem is stated
for `t ≥ 1`: the `t = 0` case would assert the trivial initial gap `Δ_0 ≤ L D`,
not provable from the per-step diameter bound alone for a *constrained* minimizer
(CLAUDE.md §1 documented deviation).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Frank–Wolfe one-step recursion** (step in Lu-BDA Thm 11.2). With
`η_t := 2 / ((t : ℝ) + 2)`, under convexity + L-smoothness + the
linear-minimization oracle + the per-step diameter bound `‖y_t - x_t‖² ≤ D`,
the optimality gap `Δ_t := f(x_t) - f(x*)` obeys
`Δ_{t+1} ≤ (1 - η_t) Δ_t + (L/2) η_t² D`. -/
lemma frankWolfe_step
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 ≤ L) (hsmooth : IsLSmooth f L)
    {X : Set E} {D : ℝ}
    (x y : ℕ → E)
    -- USER-INPUT: LMO output at each step; Lu-BDA §11.2
    (hlmo : ∀ t, y t ∈ X ∧ ∀ z ∈ X,
      ⟪gradient f (x t), y t⟫_ℝ ≤ ⟪gradient f (x t), z⟫_ℝ)
    -- USER-INPUT: per-step squared diameter bound; Lu-BDA §11.2
    (hdiam : ∀ t, ‖y t - x t‖ ^ 2 ≤ D)
    -- USER-INPUT: FW iterate update with step `2/(t+2)`; Lu-BDA §11.2 Alg.
    (hrec : ∀ t, x (t + 1) = x t + (2 / ((t : ℝ) + 2)) • (y t - x t))
    -- USER-INPUT: reference minimizer in feasible set; Lu-BDA §11.2
    {xstar : E} (hxsX : xstar ∈ X) (t : ℕ) :
    f (x (t + 1)) - f xstar
      ≤ (1 - 2 / ((t : ℝ) + 2)) * (f (x t) - f xstar)
        + (L / 2) * (2 / ((t : ℝ) + 2)) ^ 2 * D := by
  set η : ℝ := 2 / ((t : ℝ) + 2) with hη_def
  have ht2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
  have hη_nn : 0 ≤ η := by rw [hη_def]; positivity
  have hL2 : (0 : ℝ) ≤ L / 2 := by linarith
  have hη2_nn : (0 : ℝ) ≤ η ^ 2 := sq_nonneg _
  -- Step direction: `x(t+1) - x t = η • (y t - x t)`.
  have hdiff_step : x (t + 1) - x t = η • (y t - x t) := by
    rw [hrec t]; abel
  -- Inner-product reduction: `⟪∇f(x t), x(t+1) - x t⟫ = η · ⟪∇f(x t), y t - x t⟫`.
  have hinner_eq : ⟪gradient f (x t), x (t + 1) - x t⟫_ℝ
                  = η * ⟪gradient f (x t), y t - x t⟫_ℝ := by
    rw [hdiff_step, real_inner_smul_right]
  -- Norm² reduction: `‖x t - x(t+1)‖² = η² · ‖y t - x t‖²`.
  have hnorm_eq : ‖x t - x (t + 1)‖ ^ 2 = η ^ 2 * ‖y t - x t‖ ^ 2 := by
    have hflip : x t - x (t + 1) = -(η • (y t - x t)) := by
      have h1 : x t - x (t + 1) = -(x (t + 1) - x t) := by abel
      rw [h1, hdiff_step]
    rw [hflip, norm_neg, norm_smul, Real.norm_of_nonneg hη_nn]
    ring
  -- Smoothness at `(x t, x (t+1))`.
  have hsm := hsmooth (x t) (x (t + 1))
  rw [hinner_eq, hnorm_eq] at hsm
  -- LMO at `xstar` gives `⟪∇f(x t), y t⟫ ≤ ⟪∇f(x t), xstar⟫`.
  have hlmo_xs : ⟪gradient f (x t), y t⟫_ℝ ≤ ⟪gradient f (x t), xstar⟫_ℝ :=
    (hlmo t).2 xstar hxsX
  have hlmo' : ⟪gradient f (x t), y t - x t⟫_ℝ
             ≤ ⟪gradient f (x t), xstar - x t⟫_ℝ := by
    rw [inner_sub_right, inner_sub_right]; linarith
  -- Convexity gradient inequality gives `⟪∇f(x t), xstar - x t⟫ ≤ f xstar - f (x t)`.
  have hconv := inner_gradient_le_sub_of_convexOn hf hdiff (x t) xstar
  have hconv' : ⟪gradient f (x t), xstar - x t⟫_ℝ ≤ f xstar - f (x t) := by linarith
  have hkey : ⟪gradient f (x t), y t - x t⟫_ℝ ≤ f xstar - f (x t) := hlmo'.trans hconv'
  -- Multiply by `η ≥ 0`.
  have hη_step : η * ⟪gradient f (x t), y t - x t⟫_ℝ ≤ η * (f xstar - f (x t)) :=
    mul_le_mul_of_nonneg_left hkey hη_nn
  -- Diameter step: `(L/2) η² ‖y t - x t‖² ≤ (L/2) η² D`.
  have hdiam_step : (L / 2) * (η ^ 2 * ‖y t - x t‖ ^ 2) ≤ (L / 2) * (η ^ 2 * D) := by
    have h1 : η ^ 2 * ‖y t - x t‖ ^ 2 ≤ η ^ 2 * D :=
      mul_le_mul_of_nonneg_left (hdiam t) hη2_nn
    exact mul_le_mul_of_nonneg_left h1 hL2
  -- Combine: `f(x(t+1)) ≤ f(x t) + η(f xstar - f(x t)) + (L/2) η² D` and rearrange.
  nlinarith [hsm, hη_step, hdiam_step]

/-- Lu-BDA Thm 11.2 (Frank–Wolfe convergence rate). Convex `L`-smooth `f`,
convex feasible set `X` with squared diameter `≤ D`, linear-minimization oracle
`hlmo`, step `η_t = 2/(t+2)`: `f(x_t) - f(x*) ≤ 2 L D / (t+2)`.

Stated for `t ≥ 1`: the `t = 0` case would assert the trivial initial gap
`Δ_0 ≤ L D`, which is not provable from the per-step diameter bound alone for a
*constrained* minimizer; the `O(1/t)` rate is the meaningful regime, and its
base case `t = 1` follows from one FW step at `t = 0` (`η_0 = 1 ⇒ Δ_1 ≤ (L/2)D
≤ 2LD/3`). Documented deviation per CLAUDE.md §1. -/
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
    (t : ℕ) (ht : 1 ≤ t) :
    f (x t) - f xstar ≤ 2 * L * D / ((t : ℝ) + 2) := by
  have hL_nn : (0 : ℝ) ≤ L := le_of_lt hL
  have hD : (0 : ℝ) ≤ D := le_trans (sq_nonneg _) (hdiam 0)
  have hLD : (0 : ℝ) ≤ L * D := mul_nonneg hL_nn hD
  have h2LD : (0 : ℝ) ≤ 2 * L * D := by linarith
  -- Suppress the unused `hX` warning (kept in signature for book-faithfulness).
  let _ := hX
  induction t, ht using Nat.le_induction with
  | base =>
    -- Base `t = 1`: one FW step at `t = 0` (η₀ = 1) gives `Δ₁ ≤ (L/2)·D ≤ 2LD/3`.
    have hstep := frankWolfe_step hf hdiff hL_nn hsmooth x y hlmo hdiam hrec hxsX 0
    have hcast : ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) := by norm_num
    rw [hcast]
    norm_num at hstep
    nlinarith [hstep, hLD, hD, hL_nn]
  | succ k hk ih =>
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    have hk2ne : ((k : ℝ) + 2) ≠ 0 := ne_of_gt hk2
    have hk3ne : ((k : ℝ) + 3) ≠ 0 := ne_of_gt hk3
    -- Normalize the goal RHS: `↑(k+1) + 2 = ↑k + 3`.
    have hcast : (((k + 1 : ℕ) : ℝ) + 2) = (k : ℝ) + 3 := by push_cast; ring
    rw [hcast]
    -- One-step recursion at `k`.
    have hstep := frankWolfe_step hf hdiff hL_nn hsmooth x y hlmo hdiam hrec hxsX k
    have hone_sub_nn : (0 : ℝ) ≤ 1 - 2 / ((k : ℝ) + 2) := by
      rw [sub_nonneg, div_le_iff₀ hk2]; linarith
    -- Apply the inductive hypothesis through the recursion.
    have hbound1 : (1 - 2 / ((k : ℝ) + 2)) * (f (x k) - f xstar)
                ≤ (1 - 2 / ((k : ℝ) + 2)) * (2 * L * D / ((k : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left ih hone_sub_nn
    have hcombined : f (x (k + 1)) - f xstar
                  ≤ (1 - 2 / ((k : ℝ) + 2)) * (2 * L * D / ((k : ℝ) + 2))
                    + (L / 2) * (2 / ((k : ℝ) + 2)) ^ 2 * D := by linarith
    -- Closed-form simplification: the bound equals `2LD(k+1)/(k+2)²`.
    have harith : (1 - 2 / ((k : ℝ) + 2)) * (2 * L * D / ((k : ℝ) + 2))
                  + (L / 2) * (2 / ((k : ℝ) + 2)) ^ 2 * D
                = 2 * L * D * ((k : ℝ) + 1) / ((k : ℝ) + 2) ^ 2 := by
      field_simp
      ring
    rw [harith] at hcombined
    -- Telescoping arithmetic: `(k+1)(k+3) ≤ (k+2)²`.
    have hkineq : ((k : ℝ) + 1) * ((k : ℝ) + 3) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith
    -- Therefore `2LD(k+1)/(k+2)² ≤ 2LD/(k+3)`.
    have hfinal : 2 * L * D * ((k : ℝ) + 1) / ((k : ℝ) + 2) ^ 2
                ≤ 2 * L * D / ((k : ℝ) + 3) := by
      rw [div_le_div_iff₀ (by positivity) hk3]
      nlinarith [h2LD, hkineq]
    linarith

end StatLean.Optimization
