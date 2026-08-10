# Lane D — comp/r1-partitioning: LANE REPORT

## Obstructions

**None.** Every statement in the touch-set was provable exactly as frozen; no
signature, hypothesis, docstring or definition was changed. The touch-set is
0-sorry.

## Status per target

| File | Target | Status |
| --- | --- | --- |
| `Resampling/Jackknife.lean` | `jackknifed_eq` | closed |
| | `jackknifed_eq_sub_biasEstimate` | closed |
| | `jackknifePseudoValue_mcEstimate` | closed |
| | `jackknifed_mcEstimate` | closed |
| | `jackknifeVariance_mcEstimate` | closed |
| `Resampling/JackknifeBias.lean` | `integral_jackknifeMean` | closed |
| | `integral_jackknifed` | closed |
| | `jackknife_bias_reduction` | closed |
| `Partitioning/Holdout.lean` | `holdout_unbiased` | closed |
| | `holdout_integrated` | closed |
| `Partitioning/KFold.lean` | `kFold_unbiased` | closed |
| | `loo_unbiased` | closed |

## Axiom status

`Resampling/Jackknife.lean` is entirely finite algebra and all five theorems are
**axiom-clean** (`propext, Classical.choice, Quot.sound` only).

The seven measure-theoretic targets report `sorryAx` in addition. This comes
*exclusively* from the two still-sorried bricks owned by other lanes, which this
lane is permitted to use:

* `ForMathlib/PiMarginal.lean` — `pi_map_precomp_succAbove`, `pi_map_deleteSplit`
  (used by `integral_jackknifeMean` → `integral_jackknifed` →
  `jackknife_bias_reduction`, and by `integral_avg_delete_pair` → `loo_unbiased`,
  `kFold_unbiased`);
* `ForMathlib/PiMoments.lean` — `integral_avg_eval_pi` (used by
  `holdout_unbiased` → `holdout_integrated` → `kFold_unbiased`).

Closing those two files at the round gate makes the whole lane axiom-clean; no
other sorried declaration is reachable from the touch-set.

## Notes for the round gate

* `Resampling/Jackknife.lean` gained one import, `Mathlib.Algebra.BigOperators.Fin`
  (`Fin.sum_univ_succAbove` is not transitively available from
  `Core/Defs.lean`, which only pulls in `Mathlib.MeasureTheory.Measure.Dirac`).
* `Partitioning/KFold.lean` gained one same-file `private` helper,
  `integral_avg_delete_pair`: the delete-one average of a
  (training block, held-out block) score against the product law. It is the
  shared core of `loo_unbiased` (blocks = single observations, `W := Z`) and
  `kFold_unbiased` (blocks = folds, `W := Fin m → Z`, `Q := D^m`), which
  differ only in the score `F` and in how the inner integral is identified
  (`rfl` for LOO; `holdout_unbiased` for K-fold). The step
  `Q^{N+1} → Q^N ⊗ Q` is `pi_map_deleteSplit` post-composed with `Prod.swap`,
  since the brick is stated in the (deleted coordinate, rest) order.
* `Resampling/JackknifeBias.lean` gained three same-file `private` helpers
  (`measurable_comp_succAbove`, `integrable_comp_delete`,
  `integrable_jackknifeMean`) — the integrability transport along the deletion
  pushforward, needed twice.
* No `Defs.lean`, `notes/`, or out-of-lane file was touched.
