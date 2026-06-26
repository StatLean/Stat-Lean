# mt-conformal — conformal coverage (Candès L9 §9.6 Thm 2)

You are a Lean 4 proof subagent on branch `mt/conformal` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Conformal/Coverage.lean`

The merged `ForMathlib/RankUniform.lean` is imported, read-only — reuse `Exchangeable`, `rankOf`,
and **`measure_rankOf_le`** (`μ{rankOf S i ≤ k} = k/m` for `k ≤ m`). Do not touch other files.

## Goal
Prove `conformal_coverage` (0-sorry). `lake build StatLean.MultipleTesting.Conformal.Coverage` green.

## The theorem
`n+1` exchangeable, a.s. distinct scores `S : Fin (n+1) → Ω → ℝ`. With `k = ⌈(n+1)(1−α)⌉₊`,
`ENNReal.ofReal (1−α) ≤ μ{ rankOf S (Fin.last n) ≤ k }`.

## Proof roadmap (direct from rank uniformity)
1. `k := ⌈((n:ℝ)+1)*(1−α)⌉₊`. **`k ≤ n+1`**: `Nat.ceil_le.mpr`, since `(n+1)(1−α) ≤ n+1` (as
   `1−α ≤ 1` from `0 < α`; `(n+1) > 0`). So `measure_rankOf_le` applies (`m = n+1`).
2. `measure_rankOf_le S μ hmeas hExch hdistinct (Fin.last n) (hk : k ≤ n+1)` gives
   `μ{ rankOf S (last) ≤ k } = (k : ℝ≥0∞)/((n+1 : ℕ) : ℝ≥0∞)`. Rewrite the goal RHS to this.
3. **`ofReal (1−α) ≤ k/(n+1)`** (in `ℝ≥0∞`): from `Nat.le_ceil` , `(k:ℝ) ≥ (n+1)(1−α)`, so
   `(k:ℝ)/(n+1) ≥ 1−α`. Bridge to `ℝ≥0∞`: `(k:ℝ≥0∞)/((n+1):ℝ≥0∞) = ENNReal.ofReal ((k:ℝ)/(n+1))`
   (both nonneg, `n+1>0`; `ENNReal.ofReal_div_of_pos` / `ENNReal.natCast_div_le`-style — or push the
   whole thing through `ENNReal.ofReal` via `ENNReal.ofReal_natCast`), then
   `ENNReal.ofReal_le_ofReal` with `1−α ≤ (k:ℝ)/(n+1)` (`le_div_iff₀ (by positivity)`, `1−α ≥ 0`).

## Lean guidance
- `Nat.le_ceil : x ≤ ⌈x⌉₊` (for `x ≥ 0`); `Nat.ceil_le : ⌈x⌉₊ ≤ N ↔ x ≤ N`.
- ℝ≥0∞ cast/division: `ENNReal.ofReal_natCast`, `ENNReal.ofReal_div_of_pos`, `ENNReal.ofReal_le_ofReal`.
  Keep `(n+1 : ℕ)` casts consistent (`Nat.cast_add`, `Nat.cast_one`).
- `1 − α ≥ 0` from `hα1 : α < 1`.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; no anonymous `sorry`. Commit to `mt/conformal`
(`mt(conf): conformal coverage ≥ 1−α via rank uniformity (Candès L9 Thm 2)`).

## DONE
`lake build StatLean.MultipleTesting.Conformal.Coverage` exits 0; 0 sorry in the file. Report build
status, sorry count, and the `ℝ≥0∞` bridge lemmas used for step 3.
