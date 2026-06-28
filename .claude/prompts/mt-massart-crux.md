# mt-massart-crux — close countLE_reflection_bound (sharp Massart) (Candès L3 §3.3.1)

You are a Lean 4 proof subagent on branch `mt/massart-crux` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. **This is the hardest crux in the batch (Massart 1990).** Goal: 0-sorry the
file by closing `countLE_reflection_bound`. If after a serious, sustained effort the full sharp `2`
does not close, the graded fallbacks (below) are real wins — take the best one you reach.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/EmpiricalProcessSup.lean`

Read the whole file — `massart_inequality` is proved modulo the one remaining
`countLE_reflection_bound` (its docstring already analyses why union-bound/McDiarmid/maximal fail).
`ksPlus_tail_union`, `orderStat_le_iff_countLE`, `countLE_tail_le` are proved. Reuse
`StatLean/ConcentrationInequalities/` (SubGaussian, Bernstein) and
`Mathlib.Probability.Martingale.OptionalStopping` + `ForMathlib/OptionalStopping.lean`.

## Target
`countLE_reflection_bound`: `μ(⋃_{i:Fin n} {(i+1) ≤ countLE p ((i+1)/n − u)}) ≤ 2·e^{−2nu²}` for
`u ≥ √(log 2/(2n))`, independent super-uniform nulls.

## Route — exponential supermartingale + optional stopping (Massart's first-passage)
Reduce to the worst case (exact-uniform; super-uniform dominates stochastically — the indicators
`𝟙(pⱼ≤s)` have mean `≤ s`, which only helps). Set `sₖ = k/n − u` (`k = 1,…,n`), `N(s) = countLE p s`.
The event is `{∃k, N(sₖ) ≥ k}` = `{T ≤ n}` where `T = min{k : N(sₖ) ≥ k}` is the **first up-crossing**.
1. **Backward/sequential filtration & increments.** Reveal the order statistics; conditional on
   `𝓕ₖ₋₁`, `ΔNₖ = N(sₖ) − N(sₖ₋₁) ∼ Binomial(n − N(sₖ₋₁), qₖ)`, `qₖ = (sₖ − sₖ₋₁)/(1 − sₖ₋₁) = (1/n)/(1−sₖ₋₁)`.
2. **Exponential supermartingale.** For a fixed `λ > 0`, `Mₖ = exp(λ(N(sₖ) − sₖ·n) − k·ψ)`-type, OR
   directly `Mₖ = exp(λ N(sₖ))·rₖ` with the right deterministic compensator `rₖ`, is a
   `𝓕`-supermartingale (`E[e^{λΔNₖ}|𝓕ₖ₋₁] ≤ e^{λ·E[ΔNₖ|·]+λ²/8·(…)}` by Hoeffding's lemma on the
   bounded increment, tuned so the drift cancels the `−k`). Build it from
   `ProbabilityTheory.HasSubgaussianMGF` / Hoeffding-lemma bricks in `ConcentrationInequalities`.
3. **Optional stopping at `T`.** `μ{T ≤ n} ≤ μ{M_T ≥ c} ≤ E[M_T]/c ≤ E[M_0]/c` (supermartingale OST,
   `supermartingale_integral_stoppedValue_le`); choosing `λ = 4u`/the optimal value and evaluating the
   single resulting tail gives `≤ 2·e^{−2nu²}`, the `2` from the up/down boundary correction and the
   regime `u ≥ √(log 2/(2n))` absorbing the lower-order term. Mirror the Chernoff/optimization style of
   `ConcentrationInequalities/SubGaussian/Chernoff.lean`.

## Graded fallbacks (only if the sharp `2` resists)
- **(b) Clean constant `C·e^{−2nu²}`** with `C` independent of `n` (e.g. via the supermartingale with
  a non-optimal `λ`, or a dyadic peeling of `u`-levels). RESTATE `countLE_reflection_bound` /
  `massart_inequality` to the provable `C` with a CLAUDE.md §1 deviation docstring (book `2` vs `C`),
  0-sorry. This already beats the `n` factor and fully closes the file.
- **(c)** If even (b) resists, report the precise blocker and leave the single named `sorry`.

## Constraints
No `axiom`/`admit`. Document any constant deviation. Named `private` helpers only. Commit to
`mt/massart-crux` (`mt(massart): close sharp/constant one-sided KS tail via exp-supermartingale (L3 Thm 2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup` exits 0. Report: build status,
whether `countLE_reflection_bound` closed and at what constant (`2` sharp / clean `C` / sorry), the
supermartingale + OST lemmas used, and the blocker if unresolved.
