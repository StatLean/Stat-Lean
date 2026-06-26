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
`∫ E ∂μ ≤ 1`), and `E` pointwise positive. Then `1/E` is a p-variable: `μ{1/E ≤ α} ≤ α` for
`α ∈ (0,1)`; and more, `1/E` is `SuperUniform` (`μ{1/E ≤ t} ≤ ofReal t` for all `t ≥ 0`).

## Proof (Markov)
Fix `t`. For `t ≤ 0`: since `E > 0`, `1/E > 0`, so `{1/E ≤ t} = ∅` when `t < 0`, and for `t = 0`
likewise empty; the bound `≤ ofReal t` is `≤ 0`, and the empty set has measure `0`. (Handle
`t = 0` and `t < 0` up front.)
For `t > 0`: with `E ω > 0`, `1/E ω ≤ t ⟺ 1 ≤ t · E ω ⟺ E ω ≥ 1/t = t⁻¹`. So
`{ω | 1/E ω ≤ t} = {ω | t⁻¹ ≤ E ω}`. Markov's inequality for the nonnegative `E`:
`μ{t⁻¹ ≤ E} ≤ ENNReal.ofReal ((∫ E ∂μ) / t⁻¹) = ENNReal.ofReal (t · ∫ E ∂μ) ≤ ENNReal.ofReal t`
(using `∫ E ∂μ ≤ 1` and `t > 0`).

`superUniform_inv_of_isEVariable` is the same argument for all `t ≥ 0`; derive
`isPVariable_inv_of_isEVariable` from it (specialize `t = α`, `0 < α < 1 ⟹ 0 ≤ α`), or prove the
super-uniform one first and reuse.

## Lean guidance
- Markov: search `mul_meas_ge_le_integral_of_nonneg` (real, `MeasureTheory.Integral.…Markov`) or
  the ENNReal lintegral form `mul_meas_ge_le_lintegral₀`; `./tools/loogle.sh '"meas_ge_le"'`,
  `'"mul_meas_ge"'`. Integrability of `E`: `IsEVariable` gives `∫ E ∂μ ≤ 1` but you may need
  `Integrable E μ` — derive from nonneg + measurable + finite integral, or carry it via the Markov
  lemma's hypotheses; if Markov needs integrability and it is genuinely required, prove it
  (`hE.measurable`, `hE.nonneg`, and the finite integral bound) — do NOT add it as a new hypothesis.
- Set rewrite `{ω | 1/E ω ≤ t} = {ω | t⁻¹ ≤ E ω}`: `Set.ext`, then `div_le_iff`/`one_div`,
  `le_div_iff`, `inv_le_iff`, with `hpos ω` and `0 < t`. Beware `1/E ω = (E ω)⁻¹`.
- `ENNReal.ofReal` monotonicity: `ENNReal.ofReal_le_ofReal`; `ofReal (t * c) ≤ ofReal t` from
  `t * c ≤ t` (`c ≤ 1`, `t ≥ 0`) via `nlinarith`/`mul_le_of_le_one_right`.

## Constraints
No `axiom`/`admit`/new hypotheses; keep every `-- USER-INPUT:`/`-- LEAN-ONLY:` tag and the
docstrings. Any split-out lemma must be named `private`, no anonymous `sorry`. Commit to
`mt/evalues` (`mt(evalues): e→p conversion via Markov (Candès L15 Prop 3), 0-sorry`).

## DONE
`lake build StatLean.MultipleTesting.EValues.Conversion` exits 0;
`lake build … 2>&1 | grep -c sorry` is 0 for this file. Report: build status, sorry count, the
Markov lemma used, whether `Integrable E μ` was needed and how it was discharged.
