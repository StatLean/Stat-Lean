# Close the 1 remaining sorry (`good_event_highProb`) in MEstimator/GoodEvent.lean

Lean 4 / Mathlib on `StatLean` (read `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL discipline
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.GoodEvent`,
  read output directly. **NEVER** background a build, `until pgrep`/`sleep`/poll loops, nested `srun`,
  or leave `trace_state`/`#print`/`set_option` in the file. 0 errors + 0 sorries ⇒ STOP immediately.

## Scope
- **Only** fill the single `sorry` in `good_event_highProb` (the last theorem). `scoreVec_ofLp`,
  `score_linfNorm_tail`, and the private helpers are DONE — do not touch them.
- **Template:** the good-event/bad-event split in `Lasso/RandomNoise.lean` `lasso_random_rate`
  (Steps 3–6: `hexp_le`, `ht_star_sq`, `measure_union_le`, `ENNReal.ofReal_sub`, `tsub_le_iff_right`)
  is the near-exact template. READ IT.

## `good_event_highProb`
Hyps in scope: `hC : IsColumnNormalized M.X C`, `hn : 0 < n`, `hd : 0 < d`, `δ` with `0<δ<1`,
`hB : 0 < M.B`, `hCpos : 0 < C`, `hlam : 4*M.B*C*(√(log ↑d/↑n)+δ) ≤ lam`. Goal:
`ENNReal.ofReal (1 − 2*exp(−2*↑n*δ²)) ≤ μ {ω | linfNorm (scoreVec M ω) ≤ lam/2}`.

Proof:
- `hσ : 0 < M.B^2 * C^2 / ↑n := by positivity` (uses `hB`, `hCpos`, `hn`).
- `set G := {ω | linfNorm (scoreVec M ω) ≤ lam/2}`. Then `Gᶜ = {ω | lam/2 < linfNorm (scoreVec M ω)}`
  (`Set.compl_setOf` + `not_le`).
- `hlam_pos : 0 < lam` (from `hlam`: RHS `4BC(√(…)+δ) > 0` since `B,C,δ>0`, `√(…)≥0`).
- Apply `score_linfNorm_tail M C hC hn hσ (lam/2) (by positivity)`:
  `μ Gᶜ ≤ ENNReal.ofReal (2*↑d*exp(−(lam/2)²/(2*(B²C²/↑n))))`.
- `hexp : 2*↑d*exp(−(lam/2)²/(2*(B²C²/↑n))) ≤ 2*exp(−2*↑n*δ²)`. Arithmetic (mirror `lasso_random_rate`):
  let `σ² = B²C²/↑n`, `t = lam/2 ≥ 2BC(√(log d/n)+δ)`. Then `t² ≥ 4B²C²(√(log d/n)+δ)²
  ≥ 4B²C²(log d/↑n + δ²)` (drop cross term: `(a+b)² ≥ a²+b²` for `a,b≥0`, `a=√(log d/n)` needs
  `log d/n ≥ 0` from `Real.sq_sqrt`; `b=δ`). So `t²/(2σ²) ≥ 4B²C²(log d/↑n+δ²)·↑n/(2B²C²)
  = 2(log ↑d + ↑n·δ²)`, giving `2↑d·exp(−t²/(2σ²)) ≤ 2↑d·exp(−2 log ↑d − 2↑nδ²)
  = 2↑d·(↑d)^{−2}·exp(−2↑nδ²) = (2/↑d)·exp(−2↑nδ²) ≤ 2·exp(−2↑nδ²)` (since `↑d ≥ 1`).
  Tactics: `Real.exp_le_exp.mpr` for the exponent inequality (an `≤` between the exponents, via
  `nlinarith [sq_nonneg (Real.sqrt (Real.log ↑d/↑n)), Real.sq_sqrt (by positivity : (0:ℝ) ≤ log ↑d/↑n),
  Real.sqrt_nonneg _, mul_pos …]` after establishing `t ≥ …` and squaring with
  `mul_le_mul`/`pow_le_pow_left`); `Real.exp_neg`, `Real.exp_log (by positivity)`, `Real.log_pos`
  (`1 < ↑d`? need `d ≥ 1` ⇒ `↑d ≥ 1`; if `d = 1`, `log 1 = 0`, still fine — keep `↑d ≥ 1` not `> 1`).
  Final `2↑d·exp(…) ≤ 2·exp(…)` via `(2/↑d) ≤ 2` i.e. `2↑d·d^{-2} = 2/d ≤ 2` (`Nat.one_le_cast`, `div_le_self`).
- `μ Gᶜ ≤ ENNReal.ofReal (2*exp(−2↑nδ²))` (combine, `ENNReal.ofReal_le_ofReal hexp`).
- Conclude `ENNReal.ofReal (1 − 2*exp(−2↑nδ²)) ≤ μ G`: `measure_univ`, `μ univ ≤ μ G + μ Gᶜ`
  (`measure_union_le` on `G ∪ Gᶜ = univ`), `ENNReal.ofReal_sub`, `tsub_le_iff_right` — verbatim
  `lasso_random_rate` Steps 5–6. (If `1 − 2exp(…) < 0`, `ENNReal.ofReal` of it is `0 ≤ μ G` trivially.)

Report the final `lake build` line (0 sorries, 0 errors).
