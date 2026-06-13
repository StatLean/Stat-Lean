Read CLAUDE.md (repo root) first and obey it — §2, §6, §7 (esp. §7.2), §9, §10.

# CONTEXT
`StatLean/Optimization/` over a real inner product space `{E} [NormedAddCommGroup E]
[InnerProductSpace ℝ E] [CompleteSpace E]`, `⟪·,·⟫_ℝ`, gradient `gradient`/`∇`.
PROVED already (use freely, do not edit):
- `inner_gradient_le_sub_of_convexOn hf hdiff x y : f x + ⟪gradient f x, y-x⟫_ℝ ≤ f y`
- `IsLSmooth f L := ∀ x y, f y ≤ f x + ⟪∇f x, y-x⟫_ℝ + (L/2)‖x-y‖²`

# TASK — close the `sorry` in `StatLean/Optimization/FrankWolfe.lean`:
`frankWolfe_rate {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) {X : Set E} (hX : Convex ℝ X) {D : ℝ}
  (x y : ℕ → E) (hxX : ∀ t, x t ∈ X)
  (hlmo : ∀ t, y t ∈ X ∧ ∀ z ∈ X, ⟪gradient f (x t), y t⟫_ℝ ≤ ⟪gradient f (x t), z⟫_ℝ)
  (hdiam : ∀ t, ‖y t - x t‖^2 ≤ D)
  (hrec : ∀ t, x (t+1) = x t + (2/((t:ℝ)+2)) • (y t - x t))
  {xstar : E} (hxsX : xstar ∈ X) (hmin : ∀ z ∈ X, f xstar ≤ f z) (t : ℕ) :
  f (x t) - f xstar ≤ 2 * L * D / ((t:ℝ)+2)`
(Lu-BDA Thm 11.2.)

Proof outline (book §11.2) — lift the recursion to a named lemma:
1. **One-step inequality.** Let `η t := 2/((t:ℝ)+2)`, `Δ t := f (x t) - f xstar`. From `hsmooth`
   at `(x t, x (t+1))` and `hrec` (`x(t+1)-x t = η t • (y t - x t)`):
   `Δ(t+1) - Δ t = f(x(t+1)) - f(x t) ≤ η t * ⟪∇f(x t), y t - x t⟫_ℝ + (L/2) η t² ‖y t - x t‖²`.
   By the LMO (`hlmo t`, applied to `xstar ∈ X`): `⟪∇f(x t), y t⟫ ≤ ⟪∇f(x t), xstar⟫`, so
   `⟪∇f(x t), y t - x t⟫ ≤ ⟪∇f(x t), xstar - x t⟫`. By convexity
   (`inner_gradient_le_sub_of_convexOn` at `x t, xstar`): `⟪∇f(x t), xstar - x t⟫ ≤ f xstar - f(x t) = -Δ t`.
   With `hdiam t` (`‖y t - x t‖² ≤ D`): `Δ(t+1) ≤ (1 - η t) Δ t + (L/2) η t² D`.
2. **Induction on the rate.** With `η t = 2/(t+2)`, show by induction on `t` that
   `Δ t ≤ 2 L D / (t+2)`. Base `t=0`: need `Δ 0 ≤ 2LD/2 = LD` — derive from the `t=0` step
   inequality / convexity+diameter (or note `Δ 0 ≤ L D` from smoothness at `x 0, xstar` and
   `‖x0-xstar‖² ≤ D`; if the book's base needs `‖x0-xstar‖²≤D`, add it via `hdiam`-style — but
   PREFER deriving from step 1 telescoped). Inductive step: assume `Δ t ≤ 2LD/(t+2)`; plug into
   the recursion with `η t = 2/(t+2)`:
   `Δ(t+1) ≤ (1 - 2/(t+2)) 2LD/(t+2) + (L/2)(2/(t+2))² D = 2LD (t/(t+2)² + 1/(t+2)²)·… `
   simplify to `≤ 2LD/(t+3)` using `(t+1)(t+3) ≤ (t+2)²`. Close arithmetic with `nlinarith`/
   `field_simp; nlinarith` (positivity of `(t:ℝ)+2` etc.; `Nat.cast` ≥ 0).

`D ≥ 0` follows from `hdiam` + `sq_nonneg`. Need `f xstar ≤ f (x t)` (so `Δ t ≥ 0`) from `hmin`
+ `hxX t`. **Constant** `2LD/(t+2)` is the standard FW rate — should be provable as stated; if a
base-case factor forces a change, adjust ONLY the conclusion constant and document it.

If the full induction resists, prove step 1 (the recursion) as a named lemma and leave the
induction as one named `sorry`.

# TOUCH-SET — modify ONLY `StatLean/Optimization/FrankWolfe.lean`. Nothing else. Never `lake update`.

# BUILD (inside the worktree)
  lake build StatLean.Optimization.FrankWolfe
