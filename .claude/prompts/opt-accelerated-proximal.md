Read CLAUDE.md (repo root) first and obey it — §2, §6, §7 (esp. §7.2), §9, §10.

# CONTEXT
`StatLean/Optimization/` over `{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`,
`⟪·,·⟫_ℝ`, gradient `gradient`/`∇`. PROVED (use freely): `pillar` (Prox.Pillar, Lemma 12.1, see
ProximalGradient.lean for its exact shape); `IsProxMinimizer`, `proxObj` (Prox.Defs);
`IsLSmooth` (Smoothness.Defs).

# TASK — close the two `sorry`s in `StatLean/Optimization/AcceleratedProximal.lean`:

## (a) `nesterov_lambda_lower (lam : ℕ → ℝ) (hlam0 : lam 0 = 1)
  (hlamrec : ∀ t, lam (t+1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2) (t : ℕ) :
  ((t:ℝ)+2)/2 ≤ lam t`
Proof by induction on `t`. Base: `lam 0 = 1 = (0+2)/2`. Step: first `0 ≤ lam t` (from IH, since
`((t:ℝ)+2)/2 > 0`). Then `Real.sqrt (1 + 4*lam t^2) ≥ Real.sqrt (4*lam t^2) = 2*lam t`
(`Real.sqrt_le_sqrt`, `Real.sqrt_eq_iff`/`Real.sqrt_sq` with `lam t ≥ 0`; `4*lam t^2 = (2*lam t)^2`).
So `lam (t+1) = (1 + √…)/2 ≥ (1 + 2*lam t)/2 = 1/2 + lam t ≥ 1/2 + ((t:ℝ)+2)/2 = ((t:ℝ)+3)/2
= (((t+1):ℝ)+2)/2`. Close with `Real.le_sqrt`/`Real.sqrt_le_sqrt` + `nlinarith [sq_nonneg (lam t)]`.
This should fully close.

## (b) `acceleratedProximalGradient_rate {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
  (hdiff : Differentiable ℝ f) {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
  (hh : ConvexOn ℝ Set.univ h) (x y : ℕ → E) (lam : ℕ → ℝ) (hxy0 : y 0 = x 0) (hlam0 : lam 0 = 1)
  (hlamrec : …) (hxrec : ∀ t, IsProxMinimizer ((1/L)•h) (y t - (1/L)•gradient f (y t)) (x (t+1)))
  (hyrec : ∀ t, y (t+1) = x (t+1) + ((lam t - 1)/lam (t+1)) • (x (t+1) - x t))
  {xstar : E} (hmin : ∀ z, f xstar + h xstar ≤ f z + h z) (t : ℕ) :
  (f (x t) + h (x t)) - (f xstar + h xstar) ≤ 2*L*‖x 0 - xstar‖^2 / ((t:ℝ)+1)^2`
(Lu-BDA Thm 12.2.) Proof via a Lyapunov energy (book §12.2):
Let `F z := f z + h z`, `u s := lam (s-1) • x s - (xstar + (lam (s-1) - 1) • x (s-1))` (with the
`s=0` edge per book; `u 1 = x 1 - xstar`), and `Lyap s := ‖u s‖² + (2/L) * lam (s-1)^2 * (F (x s) - F xstar)`.
1. **Lyapunov antitone** (`private lemma lyapunov_antitone : ∀ s, Lyap (s+1) ≤ Lyap s`): the core,
   from `pillar` applied at `x := xstar` and at `x := x s`, `y := y s`, `yplus := x (s+1)`
   (via `hxrec s`), combined with the momentum update `hyrec` and the identity
   `λ_{s+1}² - λ_{s+1} = λ_s²` (from `hlamrec`: `λ_{s+1}` solves `z² - z - λ_s² = 0`). This is the
   hard step (book leaves it to end-of-chapter). **If you cannot fully close it, state it as a
   named `private lemma … := by sorry` and PROCEED to assemble the rate from it** — partial
   progress with one named debt is acceptable (CLAUDE.md §2).
2. **L₁ bound.** `pillar` at `x:=xstar, y:=y 0=x 0, yplus:=x 1` gives
   `(2/L)(F(x 1)-F xstar) ≤ ‖x 0-xstar‖² - ‖x 1-xstar‖²`, and `u 1 = x 1 - xstar`, `lam 0 = 1`, so
   `Lyap 1 = ‖x 1-xstar‖² + (2/L)(F(x 1)-F xstar) ≤ ‖x 0-xstar‖²`.
3. **Assemble.** By (1), `Lyap t ≤ Lyap 1 ≤ ‖x 0-xstar‖²` (for `t ≥ 1`; handle `t=0` directly:
   LHS `= 0 ≤ RHS`). Since `Lyap t ≥ (2/L) lam (t-1)² (F(x t)-F xstar)` (drop `‖u t‖²≥0`),
   `F(x t)-F xstar ≤ (L/2)‖x 0-xstar‖² / lam (t-1)²`. By `nesterov_lambda_lower`,
   `lam (t-1) ≥ ((t-1)+2)/2 = (t+1)/2`, so `lam (t-1)² ≥ (t+1)²/4` and
   `F(x t)-F xstar ≤ (L/2)‖x 0-xstar‖² · 4/(t+1)² = 2L‖x 0-xstar‖²/(t+1)²`.
   (Mind `Nat` subtraction `t-1`: split on `t = 0` vs `t = t'+1`.)

Constant `2L‖x0-x*‖²/(t+1)²` is standard FISTA — provable as stated. Use `nlinarith`/`field_simp`
+ `nesterov_lambda_lower` for the final bound.

# TOUCH-SET — modify ONLY `StatLean/Optimization/AcceleratedProximal.lean`. Nothing else.
Never `lake update`.

# BUILD (inside the worktree)
  lake build StatLean.Optimization.AcceleratedProximal
