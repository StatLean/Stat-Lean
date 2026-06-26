# Close the 3 sorries in MEstimator/GoodEvent.lean (GLM good-event high probability)

Lean 4 / Mathlib on `StatLean` (read `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL discipline (prior sessions STALLED violating this)
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.GoodEvent`,
  read output directly. **NEVER** background a build (`&`), `until pgrep`/`sleep`/poll loops, nested
  `srun`/`sbatch`, or leave `trace_state`/`#print`/`set_option` in the file. 0 errors + 0 sorries ⇒ STOP.

## Scope + template
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/GoodEvent.lean`. Keep signatures/docstrings.
- **READ `StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean` IN FULL FIRST.** Its
  `linfNorm_noise_tail` is the template for `score_linfNorm_tail`, and the good-event/bad-event split in
  `lasso_random_rate` (Steps 2–6: `Gᶜ = {t < linfNorm …}`, `measure_union_le`, `ENNReal.ofReal_sub`,
  `tsub_le_iff_right`) is the template for `good_event_highProb`. Mirror them; the differences are noted below.

## The 3 gaps

### 1. `scoreVec_ofLp` : `(scoreVec M ω).ofLp j = scoreCoord M j ω`
`scoreVec M ω = WithLp.toLp (p := 2) (fun j => scoreCoord M j ω)` (def in `GLMDefs`). So `.ofLp j` is the
function applied at `j`. Likely `rfl`, or `simp only [scoreVec, WithLp.ofLp_toLp]` / `WithLp.toLp_apply`.

### 2. `score_linfNorm_tail` — union bound over `d` coords (the `linfNorm_noise_tail` pattern)
`μ {ω | t < linfNorm (scoreVec M ω)} ≤ 2d·exp(−t²/(2·(B²C²/n)))`.
- `{ω | t < linfNorm (scoreVec M ω)} ⊆ ⋃ j, {ω | t < |(scoreVec M ω).ofLp j|}` — unfold `linfNorm` (`⨆`),
  use `lt_ciSup_iff (Set.finite_range _).bddAbove`; handle the empty-`Fin d` case (`Real.sSup_empty = 0`,
  contradicts `t ≥ 0` via `t < 0`) exactly as `linfNorm_noise_tail` does.
- Per coordinate: rewrite `(scoreVec M ω).ofLp j = scoreCoord M j ω` (`scoreVec_ofLp`). `scoreCoord M j` is
  sub-Gaussian with proxy `⟨B²C²/n, _⟩` via `score_coord_isSubGaussian M C hC hn j`, and it is **centered**
  (`IsSubGaussian` is defined on the centered variable; the mean is `0` — `score_coord_isSubGaussian`'s
  internal `hmean`). So `(score_coord_isSubGaussian …).measure_abs_sub_integral_lt_le ht` gives the two-sided
  tail `μ {ω | t < |scoreCoord M j ω − ∫…|} ≤ 2·exp(−t²/(2·(B²C²/n)))`; rewrite the `∫… = 0` (you may need to
  re-derive `∫ scoreCoord M j = 0` — reuse the `hVi`/`hmean` argument from `ScoreSubGaussian`, or extract it
  as a small `have`). Then `measure_iUnion_le` + `tsum_fintype` + `Finset.sum_le_sum` + `Finset.card_fin`,
  collapsing `∑_{j} 2·exp(…) = 2d·exp(…)` (the `linfNorm_noise_tail` Step-4 calc).

### 3. `good_event_highProb` — the `lasso_random_rate` good-event split
`λ ≥ 4BC{√(log d/n)+δ}` ⟹ `P(‖scoreVec‖∞ ≤ λ/2) ≥ 1 − 2·exp(−2nδ²)`.
- `G := {ω | linfNorm (scoreVec M ω) ≤ lam/2}`. `Gᶜ = {ω | lam/2 < linfNorm (scoreVec M ω)}`.
- Apply `score_linfNorm_tail … (lam/2) (by positivity)`: `μ Gᶜ ≤ 2d·exp(−(lam/2)²/(2·(B²C²/n)))`.
- Show that bound `≤ 2·exp(−2nδ²)`: with `σ² = B²C²/n`, `t = lam/2 ≥ 2BC{√(log d/n)+δ}`,
  `t² ≥ 4B²C²(√(log d/n)+δ)² ≥ 4B²C²(log d/n + δ²)` (drop the cross term `≥ 0`), so
  `t²/(2σ²) ≥ 4B²C²(log d/n+δ²)·n/(2B²C²) = 2(log d + nδ²)`, giving
  `2d·exp(−t²/(2σ²)) ≤ 2d·exp(−2log d − 2nδ²) = 2d·d^{−2}·exp(−2nδ²) = (2/d)·exp(−2nδ²) ≤ 2·exp(−2nδ²)` (`d ≥ 1`).
  This is the `hexp_le`/`ht_star_sq` arithmetic of `lasso_random_rate` (Steps 3) — `Real.exp_le_exp`,
  `Real.exp_log`, `nlinarith [sq_nonneg …, Real.sqrt_nonneg, …]`, `Real.log_pos`/`Real.add_pow_le_pow_mul_pow_of_sq_le`.
- Finish: `μ Gᶜ ≤ ENNReal.ofReal (2·exp(−2nδ²))`; then `1 − that ≤ μ G` via `measure_union_le`/`measure_compl`
  + `ENNReal.ofReal_sub` + `tsub_le_iff_right` (Steps 5–6 of `lasso_random_rate`, verbatim).
  (You'll need `0 ≤ 2·exp(−2nδ²) ≤ 1`? No — just mirror the `ENNReal.ofReal_sub`/`measure_univ` algebra; the
  `1 − 2e^{…}` may be negative, in which case `ENNReal.ofReal (neg) = 0 ≤ μ G` trivially — handle via `ofReal`.)

Report the final `lake build` line (0 sorries, 0 errors).
