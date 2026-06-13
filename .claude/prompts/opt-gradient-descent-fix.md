Read CLAUDE.md (repo root) first — §2, §6, §7 (ESPECIALLY §7.10: `field_simp` often closes the
goal, so a trailing `ring` raises "No goals to be solved" — drop the `ring`), §9, §10.

# CONTEXT
`StatLean/Optimization/GradientDescent.lean` already contains a COMPLETE, well-structured proof
attempt of Lu-BDA Thm 11.1 (gradient-descent rate), split into named `private lemma`s
(`gd_descent_step`, `gd_distance_step`, `gd_distance_bound`, `gd_gap_quad_bound`,
`gd_iterate_eq_xstar_of_start`, `gd_inv_gap_bound`) + the main `gradientDescent_rate`. It has
**0 sorry but does NOT compile** — 7 errors (it was never build-verified). Your ONLY job: make it
COMPILE with **0 sorry, 0 error**. Do NOT rewrite from scratch; fix in place.

`exact?`/`linarith`/`nlinarith` are available; build iteratively (command below) after each fix.

# Known errors (from the last build) and likely fixes:
- `:70:16 No goals to be solved` and `:116:16 No goals` and `:229:22 No goals` — these are
  `field_simp; ring` where `field_simp` ALREADY closed the goal (§7.10). **Delete the trailing
  `ring`** (leave just `field_simp`). Check every `field_simp; ring` / `field_simp` then `ring`
  in the file.
- `:71:2 linarith failed` and `:122:2 linarith failed` — these CASCADE from the broken `have`s
  just above (`h_coef` at ~69, `h_key`/`h_scaled` at ~113). Once those `have`s elaborate (after
  the `ring` fix), re-check; if `linarith` still fails, feed it the exact facts it needs
  (`linarith [hsm, h_coef]` etc.) or use `nlinarith` with the relevant products.
- `:238:21 rewrite failed: Did not find ... pattern` — `rw [hk_zero, hk_sq] at h_recursive`:
  the term `(f (x k) - f xstar)` / its square may not appear syntactically in `h_recursive`
  (β/assoc mismatch). Use `simp only [hk_zero, hk_sq] at h_recursive` or `nlinarith [h_recursive,
  hk_zero]` / `subst`-style instead of `rw`.
- `:276:51 unsolved goals` — in `hf_eq` the `field_simp; ring` leaves a goal: try `field_simp`
  then `ring`, or `rw [div_add_div _ _ …]`/`field_simp [hk_ne, hone_ne]; ring`. Ensure the
  nonzero side-conditions (`hk_ne`, `hone_ne`) are passed to `field_simp`.

If the final algebra of `gd_inv_gap_bound` (the `1/δ_{t+1} - 1/δ_t ≥ ω` telescoping) proves
intractable, lift JUST that one step to a named `private lemma … := by sorry` and make everything
else compile — but try to close it first.

# CONSTANT: the stated conclusion is `f (x t) - f xstar ≤ 2 * L * ‖x 0 - xstar‖^2 / (t:ℝ)`. If
your telescoping proves a different provable constant/denominator, you MAY change ONLY the RHS
numeric constant/denominator and document it in the docstring (CLAUDE.md §1). Do not change
hypotheses or variables.

# TOUCH-SET — modify ONLY `StatLean/Optimization/GradientDescent.lean`. Never `lake update`.

# BUILD (run repeatedly until green, inside the worktree)
  lake build StatLean.Optimization.GradientDescent
A clean result prints "Build completed successfully" with NO `error:` lines and NO `sorry`
warnings for this file. Commit only a compiling state.
