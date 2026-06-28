# Close #14: Le Cam functional modulus (Functional.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds. Goal 0 sorry.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/LeCam/Functional.lean`
Close the `sorry` (≈ line 113) in `minimax_functional_modulus`. The signature now has
**`(hΦlsc : LowerSemicontinuous Φ)`** (added upstream) AND `(hΦ : Monotone Φ)`. Keep signature UNCHANGED;
the proven `private` lemma `minimax_functional_pair` (lower in the file) supplies the per-pair bound. Helpers `private`.

## Strategy — two regularity gaps (both now closable)
The proof passes the per-pair bound `4⁻¹·Φ(½|θ(i)−θ(j)|) ≤ minimaxRiskDist Φ θfunc Pn` (from
`minimax_functional_pair`, for every Hellinger-admissible pair) to the supremum defining `hellingerModulus`.
1. **`IsProbabilityMeasure (P i)`**: for `n ≥ 1`, derive from `hPn i : Pn i = Measure.pi (fun _ => P i)` and
   `IsMarkovKernel Pn` (a product of `P i` is a probability measure iff each factor is; `Measure.pi`
   of probability measures, and `Pn i` is a probability measure as `IsMarkovKernel`). For `n = 0`,
   `hellingerModulus … = 0` or the bound is trivial (`Φ 0`-handling) — handle separately.
2. **sup–Φ interchange** `4⁻¹·Φ(½·⨆ d) ≤ ⨆ 4⁻¹·Φ(½·d)`: `hellingerModulus` is `⨆` over admissible pairs.
   Use `hΦlsc` (LowerSemicontinuous) + monotone: `Φ` lsc + monotone ⇒ `Φ(⨆ d) = ⨆ Φ(d)` on a directed/`⨆`
   (Mathlib `Monotone.map_iSup_of_lowerSemicontinuous` / `LowerSemicontinuous` + `iSup` continuity, or
   `Monotone.map_ciSup`/`le_iSup` per-pair then `iSup_le`). Concretely: for each pair, `4⁻¹·Φ(½ d_pair) ≤ RHS`;
   the sup over pairs of the LHS is `≥ 4⁻¹·Φ(½·⨆d)` BY lsc of `Φ` (the only place `Monotone` alone failed).
Search: `LowerSemicontinuous.map_iSup`, `Monotone.map_iSup`, `iSup_le`, `ENNReal.iSup_mul`, the
`hellingerModulus` def in `Defs.lean`.

## DONE: `lake build StatLean.Minimaxity.LeCam.Functional` green, 0 sorry. `git add` ONLY that file; commit.
