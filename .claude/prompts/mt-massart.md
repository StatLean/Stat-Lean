# mt-massart — one-sided KS statistic + Massart inequality (Candès L3 §3.3.1 Thm 2)

You are a Lean 4 proof subagent on branch `mt/massart` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/EmpiricalProcessSup.lean`

Merged & read-only: `ForMathlib/EmpiricalCDF` (`countLE`, `measurable_countLE`),
`ForMathlib/OrderStatistics` (`orderStat`, `orderStat_monotone`), `PValues/Defs` (`SuperUniform`).
You may import & use the **ConcentrationInequalities** Hoeffding bound (cross-area import is allowed
downward). Do not change the `def ksPlus` signature. Do not touch other files.

## Goal
**Prove `ksPlus_tail_union` 0-sorry (the real, achievable union bound).** Attempt
`massart_inequality` (sharp constant); if the reflection argument resists (expected — it is Massart
1990, not in Mathlib), leave it as the single named `sorry` with a one-line reason. Build green.

## `ksPlus_tail_union` roadmap (the real target — `μ{KS⁺ ≥ u} ≤ n·e^{−2nu²}`)
`ksPlus p ω = ⨆ i : Fin n, ((i+1)/n − orderStat (p·ω) i)`.
1. **Finite-sup ⇒ union.** For `n = 0`: `Fin 0` empty; handle the edge (`{u ≤ ⨆∅}` — `ciSup` of an
   empty type is `0`/default; the bound `n·… = 0` forces the event null or use `u ≥ 0`). For `n ≥ 1`:
   `u ≤ ⨆ i, f i ↔ ∃ i, u ≤ f i` (finite `ciSup` attained — `le_ciSup`/`Finset.le_sup'`,
   `exists_le_of_ciSup_le`-style). So `{ω | u ≤ ksPlus p ω} ⊆ ⋃ i, {ω | u ≤ (i+1)/n − orderStat… i}`,
   `measure_iUnion_fintype_le` (or `measure_biUnion_finset_le`) ⇒ `≤ ∑ᵢ μ{…}`.
2. **Order-stat ⇒ count.** `(k/n) − orderStat (p·ω) (k−1) ≥ u  ⟺  orderStat (p·ω) (k−1) ≤ k/n − u
   ⟺  countLE p (k/n − u) ω ≥ k`  (the `(k−1)`-th order statistic `= k`-th smallest is `≤ s` iff at
   least `k` of the `pⱼ` are `≤ s`). Prove `orderStat v i ≤ s ↔ i < (univ.filter (· ≤ s)).card`-style
   (`orderStat` is `v ∘ Tuple.sort`; relate the sorted prefix to the filter count — `Tuple.sort`
   monotonicity + `Finset.card_filter`). This `orderStat_le_iff_count` is the key `private` lemma.
3. **Hoeffding at each `k`.** `countLE p s ω = ∑ⱼ 𝟙(pⱼ ≤ s)`, independent indicators in `[0,1]` with
   `E[𝟙(pⱼ≤s)] = μ{pⱼ≤s} ≤ s` (`SuperUniform`). With `s = k/n − u`, `E[countLE] ≤ n s = k − nu`, so
   `μ{countLE ≥ k} = μ{∑(𝟙−E) ≥ k − E[∑]} ≤ μ{∑(𝟙−E) ≥ nu} ≤ exp(−2(nu)²/n) = exp(−2nu²)` by
   **Hoeffding** for sums of independent `[0,1]` variables. Search the project Hoeffding:
   `./tools/where.sh 'Hoeffding'`, `./tools/api.sh StatLean/ConcentrationInequalities/SubGaussian/Hoeffding.lean`,
   and Mathlib `'"HasSubgaussianMGF"' '"measure_sum"'`, `hasSubgaussianMGF_of_mem_Icc`. (`𝟙(pⱼ≤s)∈[0,1]`.)
4. Union over the `n` order statistics ⇒ `n·e^{−2nu²}`. ENNReal: `ENNReal.ofReal`, `Finset.sum_le_card_nsmul`.

## `massart_inequality` (sharp — likely the named debt)
The sharp `2` needs the empirical-process reflection / Massart 1990 argument (no Mathlib bricks).
Attempt only if `ksPlus_tail_union` is done with time to spare; otherwise `sorry` it with the note
"sharp DKW constant — Massart 1990 reflection argument, not in Mathlib".

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; the only acceptable residual `sorry` is `massart_inequality`. Commit to `mt/massart`
(`mt(massart): one-sided KS tail — union bound real, sharp constant debt (Candès L3 Thm 2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup` exits 0. Report build status,
sorry count (`ksPlus_tail_union` MUST be 0-sorry; `massart_inequality` 0 or 1 named sorry), the
order-stat↔count lemma, the Hoeffding lemma used, and whether the sharp bound closed.
