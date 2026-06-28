# Close the Entropy appendix sorries (Wainwright §15.4: Eq 15.60, Exercise 15.2)

Lean 4 / Mathlib proof engineer on **StatLean** (read `CLAUDE.md` §2,§6,§7). Pin `v4.29.1`. ON cluster
inside `srun` — iterate `lake build StatLean.Minimaxity.ForMathlib.Entropy` to 0 errors/0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/Entropy.lean`
Keep signatures, tags, and `**Reference.** Wainwright …` citation docstrings UNCHANGED. No
`axiom`/`admit`. Helper lemmas `private`.

## Sorries
- `discreteEntropy_nonneg` — `discreteEntropy p = ∑ negMulLog (p i)`; each `Real.negMulLog (p i) ≥ 0`
  for `p i ∈ [0,1]` (search `Real.negMulLog_nonneg`); `Finset.sum_nonneg`.
- `discreteEntropy_le_log_card` — `H(p) ≤ log|ι|`, maximised at uniform. Use concavity of `negMulLog`
  / Jensen (`Real.add_pow_le…` no; use `Real.negMulLog` + `inner_le_weight_mul_Lp` or the Gibbs route
  `∑ p log(1/p) ≤ log ∑ p·(1/p) = log|ι|` via `Real.log` concavity, `StrictConcaveOn.le_map_sum` /
  `ConcaveOn.le_map_sum` on `Real.log`). Search `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`-free routes.
- `discreteCondEntropy_le_entropy` — `H(X|Y) ≤ H(X)` ⟺ mutual information `≥ 0` (Gibbs). This is the
  log-sum inequality. If it resists honest effort, lift to a `private` lemma `mutualInfo_nonneg` with
  one `sorry` + `-- TODO(mmx): Eq 15.60a Gibbs` and report.

## DONE
`lake build StatLean.Minimaxity.ForMathlib.Entropy 2>&1 | grep -c sorry` = 0 (or only reported named
debts). Report closed/debt per lemma + key Mathlib lemmas.
