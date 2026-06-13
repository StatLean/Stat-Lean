Read CLAUDE.md (repo root) first and obey it — §2, §6, §7 (esp. §7.2 real inner product), §9, §10.

# CONTEXT
`StatLean/Optimization/` over a real inner product space `{E} [NormedAddCommGroup E]
[InnerProductSpace ℝ E] [CompleteSpace E]`, `⟪·,·⟫_ℝ`, gradient `gradient`/`∇`.
These are PROVED already (use freely, do not edit):
- `inner_gradient_le_sub_of_convexOn hf hdiff x y : f x + ⟪gradient f x, y-x⟫_ℝ ≤ f y`
  (ForMathlib.FirstOrderConvex)
- `cocoercive hf hdiff hL hsmooth x y : f x - f y ≤ ⟪∇f x, x-y⟫_ℝ - (1/(2L))‖∇f x-∇f y‖²`
  and `inner_gradient_sub_nonneg …` (Smoothness.CoCoercive, Lu-BDA Lemma 11.1)
- `gradient_eq_zero_of_forall_le hdiff hmin : gradient f x = 0` (ForMathlib.GradientCalc)
- `IsLSmooth f L := ∀ x y, f y ≤ f x + ⟪∇f x, y-x⟫_ℝ + (L/2)‖x-y‖²` (Smoothness.Defs)

# TASK — close the `sorry` in `StatLean/Optimization/GradientDescent.lean`:
`gradientDescent_rate {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (x : ℕ → E)
  (hrec : ∀ t, x (t+1) = x t - (1/L) • gradient f (x t)) {xstar : E} (hmin : ∀ y, f xstar ≤ f y)
  {t : ℕ} (ht : 0 < t) : f (x t) - f xstar ≤ 2 * L * ‖x 0 - xstar‖^2 / (t : ℝ)`
(Lu-BDA Thm 11.1.)

Proof outline (book §11.1) — lift each step to a named `private lemma` in this file so partial
progress is captured if a step resists:
1. **Per-step descent.** From `hsmooth (x t) (x (t+1))` and `hrec`, with step `1/L`:
   `f (x (t+1)) - f (x t) ≤ -(1/(2L)) * ‖gradient f (x t)‖^2`.  (Substitute
   `x(t+1)-x t = -(1/L)•∇f(x t)`; `⟪∇,(-(1/L))∇⟫ = -(1/L)‖∇‖²`, `(L/2)‖(1/L)∇‖² = (1/(2L))‖∇‖²`.)
2. **Distance non-increasing.** `‖x (t+1) - xstar‖^2 ≤ ‖x t - xstar‖^2`. Expand
   `‖x t - (1/L)∇f(x t) - xstar‖²` and use `inner_gradient_sub_nonneg` with `gradient f xstar = 0`
   (`gradient_eq_zero_of_forall_le hdiff hmin`): the cross term dominates. Hence by induction
   `‖x t - xstar‖ ≤ ‖x 0 - xstar‖` for all `t`.
3. **Gap bound.** Let `δ t := f (x t) - f xstar ≥ 0`. Convexity (`inner_gradient_le_sub_of_convexOn`
   at `x t, xstar`) + Cauchy–Schwarz (`real_inner_le_norm`): `δ t ≤ ⟪∇f(x t), x t - xstar⟫_ℝ ≤
   ‖x t - xstar‖ * ‖∇f(x t)‖ ≤ ‖x 0 - xstar‖ * ‖∇f(x t)‖`. Combined with step 1:
   `δ (t+1) ≤ δ t - (1/(2L)) ‖∇f(x t)‖² ≤ δ t - (1/(2L‖x0-xstar‖²)) δ t²`.
4. **Rate.** With `ω := 1/(2L‖x0-xstar‖²)`: `δ(t+1) ≤ δ t - ω δ t²` and `δ` nonneg-decreasing
   give `1/δ(t+1) - 1/δ t ≥ ω`, so `1/δ t ≥ ω·t` (telescub from `t=0`), i.e.
   `δ t ≤ 1/(ω t) = 2L‖x0-xstar‖²/t`. Handle the `δ t = 0` and `‖x0-xstar‖ = 0` degenerate cases
   (then `δ ≡ 0`) separately.

**Constant freedom (CLAUDE.md §1 + TODO):** the book's `2L/t` is loose. You MAY change ONLY the
numeric constant / denominator in the conclusion's RHS to the value your telescoping actually
proves (e.g. `… / (t)` vs `/(t-1)`, or numerator `L/2`), and document the change in the docstring.
Do NOT change hypotheses, variables, or the `x 0`/`xstar` structure. If you cannot close the full
rate, prove steps 1–3 as named lemmas and leave step 4 as a single named `sorry` lemma.

# TOUCH-SET — modify ONLY `StatLean/Optimization/GradientDescent.lean`. Nothing else. Never `lake update`.

# BUILD (inside the worktree)
  srun -p shared -c 8 --mem=24G -t 0:50:00 lake build StatLean.Optimization.GradientDescent
