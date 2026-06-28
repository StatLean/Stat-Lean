# mt-massart-sharp — close the sharp one-sided DKW/Massart constant (Candès L7 §3.3.1)

You are a Lean 4 proof subagent on branch `mt/massart-sharp` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`. **This is a research-level result (Massart 1990).** Make
a genuine attempt; the success criterion is graded (see DONE) — improving the constant from the
proved `n·e^{−2nu²}` toward `2·e^{−2nu²}` is real progress even if you don't reach the sharp constant.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/EmpiricalProcessSup.lean`

The union bound `ksPlus_tail_union` (`μ{KS⁺≥u} ≤ n·e^{−2nu²}`) is proved (reuse it + its helpers
`orderStat_le_iff_countLE`, `countLE_tail_le`). The remaining `sorry` is `massart_inequality`
(`μ{KS⁺≥u} ≤ 2·e^{−2nu²}` for `u ≥ √(log 2/(2n))`). Do NOT change signatures.

## Routes (try in order; the project's empirical-process library may help — explore it)
First survey what's available: the project has substantial empirical-process machinery in
`StatLean/AsymptoticStatistics/EmpiricalProcess/` (`GlivenkoCantelli`, `Donsker`, `MaximalOrlicz`,
`DonskerBracketing`) and concentration in `StatLean/ConcentrationInequalities/`
(`SubGaussian`, `Maximal`, `McDiarmid`). `./tools/api.sh` / `./tools/where.sh` them.

1. **Reflection / exponential-supermartingale (sharp route).** The one-sided sup of the empirical
   process admits a finite-`n` exponential supermartingale: for the partial-sum reformulation
   `F̂ₙ(t)−t = (1/n)∑ᵢ(𝟙(pᵢ≤t)−t)`, the process indexed by the sorted p-values has negatively-associated
   increments, and `Mₖ = exp(λ Sₖ − ψ(λ)k)`-type bounds give a constant factor via optional stopping
   on the first up-crossing of level `u`. Search `'"reflection"'`, `'"hitting"'`, optional-stopping
   in `Mathlib.Probability.Martingale.OptionalStopping` + the project `ForMathlib/OptionalStopping`.
2. **McDiarmid / bounded-differences (clean constant).** `KS⁺` is a function of the `n` independent
   `pᵢ` with bounded differences `1/n` each, so McDiarmid
   (`StatLean/ConcentrationInequalities/McDiarmid`) gives
   `μ{KS⁺ ≥ E[KS⁺] + ε} ≤ e^{−2nε²}`; combine with a bound `E[KS⁺] ≤ √(…/n)` (a maximal/expectation
   bound on the one-sided sup — `Maximal/` or a direct order-statistic argument) to reach a
   constant-factor `C·e^{−2nu²}`. This is the most likely-to-close route for a clean (if not perfectly
   sharp) constant; it removes the `n` factor.

If you reach `2·e^{−2nu²}`, great. If you reach a clean constant `C` (e.g. via McDiarmid) that beats
the `n` factor, RESTATE `massart_inequality` to that provable constant with a docstring noting the
deviation from the book's `2` (CLAUDE.md §1 — state the provable constant), and prove it 0-sorry.
If neither closes, leave the `sorry` but report the precise blocker.

## Constraints
No `axiom`/`admit`. If you restate the constant, document it (book `2` vs provable `C`). Named
`private` helpers only. Commit to `mt/massart-sharp`
(`mt(massart): sharp/constant-factor one-sided KS tail (Candès L3 Thm 2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup` exits 0. Report: build status,
whether `massart_inequality` closed and at what constant (`2` sharp / a clean `C` / still `sorry`),
which route/lemmas you used, and the blocker if unresolved.
