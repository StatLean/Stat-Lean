# mt-empirical-cdf — empirical CDF + counting processes (Candès L3)

You are a Lean 4 proof subagent on branch `mt/empirical-cdf` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/EmpiricalCDF.lean`

Do **NOT** change the `def` signatures of `countLE`, `nullCountLE`, `empiricalCDF` — downstream
units (BH-dependence, reverse-martingale, Storey, KS) depend on them as the public interface. Do
not touch any other file. You MAY add `private` helper lemmas within the touch-set.

## Goal
Close all 8 `sorry`s to 0-sorry / 0-error. Verify
`lake build StatLean.MultipleTesting.ForMathlib.EmpiricalCDF` green.

## The lemmas (all elementary)
`countLE p t ω = (univ.filter (p · ω ≤ t)).card` (= R(t)); `nullCountLE H₀ p t ω =
(H₀.filter (p · ω ≤ t)).card` (= V(t)); `empiricalCDF p t ω = R(t)/n`.

1. `countLE_le` — `Finset.card_filter_le` then `Finset.card_univ`/`Fintype.card_fin`.
2. `countLE_mono` (`s ≤ t`) — `{j | pⱼ≤s} ⊆ {j | pⱼ≤t}` (`Finset.filter_subset_filter` /
   `Finset.monotone_filter_right` with `pⱼ≤s → pⱼ≤t` from `le_trans · hst`), then
   `Finset.card_le_card`.
3. `nullCountLE_le_countLE` — `H₀.filter P ⊆ univ.filter P` (subset on the base set via
   `Finset.filter_subset_filter` after `H₀ ⊆ univ`, or `Finset.monotone_filter_left`);
   `Finset.card_le_card`.
4. `nullCountLE_mono` — like (2) on base `H₀`.
5. `measurable_countLE` — rewrite `card` of a filter as a sum of indicators:
   `Finset.card_filter : (s.filter P).card = ∑ j ∈ s, if P j then 1 else 0`. Then
   `Finset.measurable_sum`; each summand `fun ω => if pⱼ ω ≤ t then 1 else 0` is measurable via
   `Measurable.ite (measurableSet_le (hp j) measurable_const) measurable_const measurable_const`
   (or `(measurableSet_le (hp j) measurable_const).indicator`-style). Search:
   `./tools/loogle.sh '"card_filter"'`, `'"measurableSet_le"'`, `'"measurable_sum"'`.
6. `measurable_nullCountLE` — identical, base `H₀`.
7. `empiricalCDF_nonneg` — `div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)`.
8. `empiricalCDF_le_one` — `R(t) ≤ n` (lemma 1) ⟹ `(R:ℝ)/n ≤ 1`. For `n = 0`, `R(t) = 0` (no
   `Fin 0`), so `0/0 = 0 ≤ 1`; otherwise `div_le_one (by positivity)` + cast of `countLE_le`.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings and the citation. Named `private` helpers only.
Commit to `mt/empirical-cdf` (`mt(empcdf): empirical CDF + R(t)/V(t) counts (Candès L3), 0-sorry`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.EmpiricalCDF` exits 0; `grep -c sorry` is 0 for the
file. Report build status, sorry count, any helper lemmas added.
