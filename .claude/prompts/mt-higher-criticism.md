# mt-higher-criticism — detection boundary properties (Candès L3 §3.3.3)

You are a Lean 4 proof subagent on branch `mt/higher-criticism` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/GoodnessOfFit/HigherCriticism.lean`

Merged & read-only: `ForMathlib/EmpiricalCDF`. Do not change the `def rhoStar` / `def hcStat`
signatures or the module docstring (it documents the deferred Donoho–Jin theorem honestly — do NOT
add a laundered detection theorem).

## Goal
Close the **3 boundary-property sorries** (`rhoStar_continuous_at_junction`, `rhoStar_nonneg`,
`rhoStar_one`) to 0-sorry. These are the genuinely-formalizable facts about the detection boundary
`ρ*(β) = if β < 3/4 then β−1/2 else (1−√(1−β))²`. `lake build
StatLean.MultipleTesting.GoodnessOfFit.HigherCriticism` green.

## The lemmas (elementary real analysis)
1. `rhoStar_continuous_at_junction`: `3/4 − 1/2 = (1 − √(1 − 3/4))²`. Note `1 − 3/4 = 1/4`,
   `√(1/4) = 1/2` (`Real.sqrt_eq_iff` / `Real.sqrt_eq_one`-style, or `show √(1/4)=1/2` via
   `Real.sqrt_eq_iff_sq_eq` / `Real.sqrt_eq_iff_mul_self_eq`); then `(1−1/2)² = 1/4 = 3/4−1/2`
   (`norm_num`).
2. `rhoStar_nonneg` (`1/2 < β`, `β ≤ 1`): unfold `rhoStar`, `split_ifs`:
   - `β < 3/4`: `β − 1/2 ≥ 0` from `1/2 < β` (`linarith`).
   - `β ≥ 3/4`: `(1 − √(1−β))² ≥ 0` by `sq_nonneg`.
3. `rhoStar_one`: `rhoStar 1`; `1 < 3/4` is false so the `else` branch: `(1 − √(1−1))² = (1−√0)²
   = (1−0)² = 1` (`Real.sqrt_zero`, `norm_num`); the `if` guard `(1 : ℝ) < 3/4` is `False`
   (`by norm_num`), so `if_neg`.

Search: `./tools/loogle.sh '"sqrt_eq"'`, `'"sqrt_zero"'`, `Real.sqrt_eq_one`.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + the deferral note. Named `private` helpers only;
no anonymous `sorry` (all 3 must close). Do NOT add a `higher_criticism_detects` theorem — the full
Donoho–Jin detection theorem is honestly deferred in the docstring (it needs the empirical-process
LIL + sparse-mixture large deviations not yet in the library; the project's `IsPDonsker` covers only
the H₀ convergence half). Commit to `mt/higher-criticism`
(`mt(hc): detection boundary ρ*(β) + properties; HC statistic (Candès L3 §3.3.3)`).

## DONE
`lake build StatLean.MultipleTesting.GoodnessOfFit.HigherCriticism` exits 0; 0 sorry. Report build
status, sorry count, and the sqrt lemmas used.
