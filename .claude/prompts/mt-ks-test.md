# mt-ks-test — Kolmogorov–Smirnov test level (Candès L3 §3.3.1)

You are a Lean 4 proof subagent on branch `mt/ks-test` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/GoodnessOfFit/KolmogorovSmirnov.lean`

Merged & read-only: `ForMathlib/EmpiricalProcessSup` — reuse `ksPlus` and the proved
**`ksPlus_tail_union`** (`μ{u ≤ ksPlus p} ≤ ofReal(n·e^{−2nu²})` for `u ≥ 0`). Do not touch others.

## Goal
Prove `ks_test_level` (0-sorry). `lake build StatLean.MultipleTesting.GoodnessOfFit.KolmogorovSmirnov` green.

## The theorem & proof (elementary — plug the threshold into the union tail)
`u_α := √(log(n/α)/(2n))`. Show `μ{ u_α ≤ ksPlus p } ≤ ofReal α`.
1. `u_α ≥ 0` (`Real.sqrt_nonneg`). Apply `ksPlus_tail_union μ p hmeas hindep hnull (hu := …)`:
   `μ{u_α ≤ ksPlus p} ≤ ofReal (n · e^{−2n·u_α²})`.
2. **Simplify `n · e^{−2n·u_α²} = α`**:
   - `u_α² = log(n/α)/(2n)` by `Real.sq_sqrt` (arg `≥ 0`: `log(n/α) ≥ 0` since `n/α ≥ 1`, as
     `α < 1 ≤ n` ⇒ `α ≤ n`; `Real.log_nonneg`, `one_le_div`).
   - `−2n·u_α² = −log(n/α)`, so `e^{−2n·u_α²} = e^{−log(n/α)} = (n/α)⁻¹ = α/n`
     (`Real.exp_neg`, `Real.exp_log` with `n/α > 0`).
   - `n · (α/n) = α` (`n ≠ 0`).
3. Conclude `μ{u_α ≤ ksPlus p} ≤ ofReal α` (`congr`/`le_of_le_of_eq`).

`./tools/loogle.sh '"sq_sqrt"'`, `'"exp_log"'`, `'"log_nonneg"'`, `'"one_le_div"'` as needed.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; no anonymous `sorry`. Commit to `mt/ks-test`
(`mt(ks): Kolmogorov–Smirnov test level ≤ α via KS⁺ union tail (Candès L3)`).

## DONE
`lake build StatLean.MultipleTesting.GoodnessOfFit.KolmogorovSmirnov` exits 0; 0 sorry. Report build
status, sorry count.
