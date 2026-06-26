# mt-hc-cruxes — close the 3 Higher-Criticism Donsker cruxes (Candès L3 §3.3.3)

You are a Lean 4 proof subagent on branch `mt/hc-cruxes` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain `lake build`,
ITERATE. **Goal: 0-sorry the file** — close the 3 named cruxes so `halfLine_isPDonsker` (the H₀
empirical-CDF Donsker theorem) is fully real. Do NOT touch `rhoStar`/`hcStat`/the deferral docstring,
and do NOT add a laundered detection theorem.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/GoodnessOfFit/HigherCriticism.lean`

The 3 `sorry`s are `halfLineClass_bracketingEntropyIntegral_lt_top`, `halfLineClass_J_pos`,
`halfLineClass_chain_bound`. **READ the project's empirical-process library FIRST** — the exact
definitions of bracketing number / entropy integral / the chaining hypotheses live there, and you
must match them precisely:
`./tools/api.sh StatLean/AsymptoticStatistics/EmpiricalProcess/DonskerBracketing.lean`,
`.../FunctionClass.lean`, `.../Donsker.lean`, `.../MaximalOrlicz.lean`. Get the **exact signature** of
`isPDonsker_of_finite_bracketing_entropy_integral` and of `bracketingEntropyIntegral` / the bracketing
number `N_[]`.

## Crux A — `halfLineClass_bracketingEntropyIntegral_lt_top` (the genuine half-line crux)
The half-line class `F = {𝟙(−∞,t] : t∈ℝ}` has **bracketing number `N_[](ε, F, L²(P)) ≤ ⌈1/ε²⌉ + 1`**:
partition `[0,1]` into `m = ⌈1/ε²⌉` equal-`P`-mass pieces by the quantiles `t₀=−∞ < t₁ < … < t_m=+∞`
with `P((tᵢ₋₁,tᵢ]) ≤ ε²`; the brackets `[𝟙(−∞,tᵢ₋₁], 𝟙(−∞,tᵢ]]` cover `F` and have
`L²(P)`-size `‖𝟙(−∞,tᵢ] − 𝟙(−∞,tᵢ₋₁]‖_{L²(P)} = √(P((tᵢ₋₁,tᵢ])) ≤ ε`. Hence
`log N_[](ε) ≤ 2 log(1/ε) + O(1)`, and the entropy integral `∫₀¹ √(log N_[](ε)) dε < ∞`
(`∫₀¹ √(log(1/ε)) dε = √(π)/2 < ∞` — search `'"integral"' '"sqrt"' '"log"'`, or bound
`√(log(1/ε)) ≤ 1/√ε` and `∫₀¹ ε^{−1/2} dε = 2`). The quantile grid uses the (generalized inverse of
the) CDF of `P`; if constructing exact quantiles is painful, use the **cruder** monotone grid that
the project's `N_[]` definition admits, or bound `N_[]` by a covering of the *range* `[0,1]` of the
CDF into `⌈1/ε²⌉` levels. Match the project's exact `bracketingEntropyIntegral … < ⊤` statement.

## Cruxes B,C — `halfLineClass_J_pos`, `halfLineClass_chain_bound` (framework regularity)
These were introduced as regularity inputs to `isPDonsker_of_finite_bracketing_entropy_integral`.
**First check whether they are actually hypotheses of that theorem at all** — re-read its signature;
the previous pass may have over-decomposed. If they are NOT needed, delete them and feed
`isPDonsker_of_finite_bracketing_entropy_integral` directly (`halfLineClass_measurable` +
`halfLineClass_bracketingEntropyIntegral_lt_top` + whatever it actually requires). If they ARE genuine
hypotheses:
- `J_pos`: the entropy integral is `> 0` for `δ' > 0` — the class has ≥ 2 distinct elements (any two
  distinct half-lines differ on a positive-`P`-measure set when `P` is nondegenerate; if `P` can be a
  point mass handle that edge), so `N_[] ≥ 2`, `log N_[] ≥ log 2 > 0`, integral `> 0`. Elementary.
- `chain_bound`: match the exact chaining inequality the framework states; it is generic (not
  half-line-specific) — discharge it from the entropy bound in (A) + the project's chaining lemmas.

## Constraints
No `axiom`/`admit`; no laundered detection theorem; keep `rhoStar`/`hcStat`/deferral docstring. Named
`private`/`theorem` helpers only. Commit to `mt/hc-cruxes`
(`mt(hc): close half-line bracketing-entropy + framework cruxes ⇒ halfLine_isPDonsker real`).

## DONE
`lake build StatLean.MultipleTesting.GoodnessOfFit.HigherCriticism` exits 0. Report build status,
final sorry count + which cruxes closed, whether J_pos/chain_bound were actually needed, and the
entropy-integral bound used.
