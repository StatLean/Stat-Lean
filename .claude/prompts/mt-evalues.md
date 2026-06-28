# mt-evalues — e-value → p-value conversion (Candès L15, Prop. 3)

You are a Lean 4 proof subagent on branch `mt/evalues` (based on `mt/batch8`). Project:
**StatLean** — read its `CLAUDE.md` first (§2 hypothesis discipline, §6 search, §7 gotchas, §9).
You are inside an `srun` allocation — build with plain `lake build`, ITERATE until 0 errors / 0
sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/EValues/Conversion.lean`

Do **NOT** touch `EValues/Defs.lean` or `PValues/Defs.lean` (laptop-only), the umbrella, or any
other file. You MAY add `private` helper lemmas *within the touch-set file*.

## Goal
Close the two `sorry`s — `isPVariable_inv_of_isEVariable` and `superUniform_inv_of_isEVariable` —
to 0-sorry, 0-error. Do not weaken or add hypotheses to either public signature.
Verify: `lake build StatLean.MultipleTesting.EValues.Conversion` green.

## The result (Candès, Lecture 15, Prop. 3, STAT 300C)
`E` an e-variable for the simple null `μ` (`IsEVariable`: `∀ω, 0 ≤ E ω`, `Measurable E`,
`expectation_le_one : ∫⁻ ω, ENNReal.ofReal (E ω) ∂μ ≤ 1`), and `E` pointwise positive. Then `1/E`
is a p-variable: `μ{1/E ≤ α} ≤ α` for `α ∈ (0,1)`; and more, `1/E` is `SuperUniform`
(`μ{1/E ≤ t} ≤ ofReal t` for all `t ≥ 0`).

NOTE the e-variable's defining bound is now a **lintegral** `∫⁻ ofReal(E) ∂μ ≤ 1` (field
`expectation_le_one`), not a Bochner integral — this is the genuine `Eμ[E] ≤ 1` for the nonneg `E`
and forces finiteness. Use the lintegral Markov directly; no Bochner↔lintegral detour needed.

## Proof (lintegral Markov)
Fix `t`. For `t ≤ 0`: since `E > 0`, `1/E > 0`, so `{1/E ≤ t} = ∅`; the bound `ofReal t ≥ 0` holds
and the empty set has measure `0`. (Handle `t ≤ 0` up front.)
For `t > 0`: with `E ω > 0`, `1/E ω ≤ t ⟺ E ω ≥ t⁻¹ ⟺ ofReal t⁻¹ ≤ ofReal (E ω)`. So
`{ω | 1/E ω ≤ t} = {ω | ofReal t⁻¹ ≤ ofReal (E ω)}`. lintegral Markov:
`μ{ofReal t⁻¹ ≤ ofReal∘E} ≤ (∫⁻ ofReal∘E ∂μ) / ofReal t⁻¹ ≤ 1 / ofReal t⁻¹ = ofReal t`
(using `expectation_le_one` and `(ofReal t⁻¹)⁻¹ = ofReal t` for `t > 0`).

`superUniform_inv_of_isEVariable` is the all-`t ≥ 0` form; derive
`isPVariable_inv_of_isEVariable` from it (specialize `t = α`).

## Lean guidance
- lintegral Markov: `meas_ge_le_lintegral_div` (`μ{g ≥ ε} ≤ (∫⁻ g)/ε` for measurable nonneg `g`,
  `ε ≠ 0,∞`) or `mul_meas_ge_le_lintegral₀`. Search `./tools/loogle.sh '"meas_ge_le_lintegral"'`,
  `'"lintegral_div"'`. `g := fun ω => ENNReal.ofReal (E ω)` is measurable (`hE.measurable`,
  `ENNReal.measurable_ofReal.comp`); `ε := ENNReal.ofReal t⁻¹` (`≠ 0` since `t⁻¹ > 0`; `≠ ∞`).
- Set rewrite `{ω | 1/E ω ≤ t} = {ω | ofReal t⁻¹ ≤ ofReal (E ω)}`: `Set.ext`; `1/E ω = (E ω)⁻¹`;
  `(E ω)⁻¹ ≤ t ⟺ t⁻¹ ≤ E ω` (`inv_le_comm₀`/`le_inv_comm₀`/`one_div`, `hpos ω`, `0 < t`); then
  `ENNReal.ofReal_le_ofReal_iff` (both sides `≥ 0`) to move to `ofReal`.
- Finish: `ENNReal.div_le_iff` / `ENNReal.le_div_iff_mul_le`; `ENNReal.ofReal_inv_of_pos` to compute
  `(ofReal t⁻¹)⁻¹ = ofReal t`. If you instead prefer the real Markov route, integrability of `E` is
  derivable from `expectation_le_one` (`∫⁻ ofReal∘E < ∞`) + nonneg + measurable
  (`integrable_iff_lintegral_ofReal_lt_top`-style) — but the lintegral route above avoids it.

## Constraints
No `axiom`/`admit`/new hypotheses; keep every `-- USER-INPUT:`/`-- LEAN-ONLY:` tag and the
docstrings. Any split-out lemma must be named `private`, no anonymous `sorry`. Commit to
`mt/evalues` (`mt(evalues): e→p conversion via Markov (Candès L15 Prop 3), 0-sorry`).

## DONE
`lake build StatLean.MultipleTesting.EValues.Conversion` exits 0;
`lake build … 2>&1 | grep -c sorry` is 0 for this file. Report: build status, sorry count, the
Markov lemma used, whether `Integrable E μ` was needed and how it was discharged.
