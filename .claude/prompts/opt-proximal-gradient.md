Read CLAUDE.md (repo root) first and obey it — §2, §6, §7 (esp. §7.2), §9, §10.

# CONTEXT
`StatLean/Optimization/` over `{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`,
`⟪·,·⟫_ℝ`, gradient `gradient`/`∇`. PROVED (use freely, do not edit):
- `pillar hf hdiff hL hsmooth hh (hyplus : IsProxMinimizer ((1/L)•h) (y - (1/L)•∇f y) yplus) :
   (f yplus + h yplus) - (f x + h x) ≤ (L/2)*‖x-y‖^2 - (L/2)*‖x-yplus‖^2`  (Prox.Pillar, Lemma 12.1)
- `IsProxMinimizer h x z`, `proxObj` (Prox.Defs); `IsLSmooth` (Smoothness.Defs).

# TASK — close the `sorry` in `StatLean/Optimization/ProximalGradient.lean`:
`proximalGradient_rate {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h) (x : ℕ → E)
  (hrec : ∀ t, IsProxMinimizer ((1/L)•h) (x t - (1/L)•gradient f (x t)) (x (t+1)))
  {xstar : E} (hmin : ∀ y, f xstar + h xstar ≤ f y + h y) {t : ℕ} (ht : 0 < t) :
  (f (x t) + h (x t)) - (f xstar + h xstar) ≤ L * ‖x 0 - xstar‖^2 / (2*(t:ℝ))`
(Lu-BDA Thm 12.1.) Let `F z := f z + h z`, `δ s := F (x s) - F xstar`.

Proof (book §12.1) — lift sub-steps to named lemmas:
1. **Monotone descent.** Apply `pillar … (hrec t)` with `x := x t, y := x t, yplus := x (t+1)`
   (note `hrec t` is exactly the needed `IsProxMinimizer ((1/L)•h) (x t - (1/L)•∇f(x t)) (x(t+1))`):
   `F (x (t+1)) - F (x t) ≤ (L/2)‖x t - x t‖² - (L/2)‖x t - x(t+1)‖² = -(L/2)‖x(t+1)-x t‖² ≤ 0`.
   So `δ` is antitone: `δ (s+1) ≤ δ s`, hence `δ t ≤ δ s` for `s ≤ t`.
2. **Telescoping.** Apply `pillar … (hrec s)` with `x := xstar, y := x s, yplus := x (s+1)`:
   `δ (s+1) = F (x (s+1)) - F xstar ≤ (L/2)‖xstar - x s‖² - (L/2)‖xstar - x (s+1)‖²`.
   Sum `s = 0 .. t-1` (`Finset.sum_range_succ` / `Finset.sum_range` telescoping of the RHS):
   `∑_{s<t} δ (s+1) ≤ (L/2)‖xstar - x 0‖² - (L/2)‖xstar - x t‖² ≤ (L/2)‖x 0 - xstar‖²`
   (`norm_sub_rev`; drop the nonneg `(L/2)‖xstar-x t‖²`).
3. **Combine.** By step 1, each `δ (s+1) ≥ δ t` for `s+1 ≤ t`, so `∑_{s<t} δ(s+1) ≥ t • δ t`.
   Therefore `(t:ℝ) * δ t ≤ (L/2)‖x 0 - xstar‖²`, giving
   `δ t ≤ L‖x 0 - xstar‖²/(2t)`. (Divide by `t>0`; `ht : 0 < t`.)
   Need `δ s ≥ 0` from `hmin` for the monotonicity/positivity bookkeeping.

Constant `L‖x0-x*‖²/(2t)` is standard and should be provable as stated. Use `Finset.sum_range`,
`Finset.sum_le_sum`, `nlinarith`/`field_simp` for the final division.

# TOUCH-SET — modify ONLY `StatLean/Optimization/ProximalGradient.lean`. Nothing else. Never `lake update`.

# BUILD (inside the worktree)
  srun -p shared -c 8 --mem=24G -t 0:50:00 lake build StatLean.Optimization.ProximalGradient
