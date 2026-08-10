# Lane A — `comp/r1-core`: PiMoments + EmpiricalMeasure + Monte Carlo estimation

**Status: all 19 targets closed. 0 sorries, 0 errors, 0 obstructions.**

Every headline target was checked with `#print axioms` in a temporary scratch section
(since deleted) and depends only on `propext, Classical.choice, Quot.sound`.

## Per-target

### `StatLean/ComputationalStatistics/ForMathlib/PiMoments.lean` — 0 sorries

| target | status |
| --- | --- |
| `integral_avg_eval_pi` | closed |
| `variance_avg_eval_pi` | closed |
| `integral_sq_dev_avg_eval_pi` | closed |
| `tendsto_avg_eval_infinitePi` | closed |

Three same-file `private` helpers were added: `mp_eval` (coordinate reads of
`Measure.pi` are measure preserving), `integrable_eval_pi`, `integral_eval_pi`.

Route notes:

* `variance_avg_eval_pi` did **not** need the sketched
  `iIndepFun_pi` + `IndepFun.variance_sum` assembly: the pin already carries
  `ProbabilityTheory.variance_sum_pi`
  (`Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i]`,
  `Mathlib/Probability/Moments/Variance.lean`), which is exactly the statement at
  the constant family `X i := g`.  Only a `funext` to turn the `Finset.sum` of
  functions into `fun x => ∑ i, g (x i)` plus `variance_const_mul` was needed.
* `integral_sq_dev_avg_eval_pi` is the sketched route: `variance_eq_integral` on
  the average, with its mean supplied by `integral_avg_eval_pi`.
* `tendsto_avg_eval_infinitePi` did **not** need any hand derivation of the
  coordinate independence under `infinitePi`: the pin has
  `ProbabilityTheory.iIndepFun_infinitePi` and
  `measurePreserving_eval_infinitePi`.  A new import,
  `Mathlib.Probability.Independence.InfinitePi`, was added for the former.

### `StatLean/ComputationalStatistics/Core/EmpiricalMeasure.lean` — 0 sorries

All 11 targets closed: `isProbabilityMeasure_empiricalMeasure`,
`empiricalMeasure_apply`, `integral_empiricalMeasure`,
`lintegral_empiricalMeasure`, `isProbabilityMeasure_weightedMeasure`,
`integral_weightedMeasure`, `empiricalMeasure_eq_weightedMeasure`,
`integral_categorical`, `isProbabilityMeasure_categorical`,
`weightedMeasure_eq_map_categorical`, `empiricalMeasure_eq_map_categorical`.

All follow the sketched `Measure.smul_apply` / `Measure.finset_sum_apply` /
`Measure.dirac_apply'` expansions.  Two deviations worth recording:

* `integral_empiricalMeasure` / `integral_weightedMeasure` need Dirac
  integrability, supplied by `MeasureTheory.integrable_dirac'` (the primed form
  takes `StronglyMeasurable`, matching the frozen LEAN-ONLY hypothesis) plus
  `Integrable.smul_measure` for the weighted case.
* `weightedMeasure_eq_map_categorical` is proved by `Measure.ext` on measurable
  sets rather than by pushing `Measure.map` through the `Finset.sum` — the
  set-level route avoids needing a `Measure.map_finset_sum`, which the pin does
  not have as a standalone lemma.  No measurability hypothesis on `x` is needed
  (`Measurable.of_discrete`), as the docstring promises.

### `StatLean/ComputationalStatistics/MonteCarlo/Estimation.lean` — 0 sorries

| target | status |
| --- | --- |
| `mcEstimate_unbiased` | closed (term-mode wrapper) |
| `mcEstimate_variance` | closed (term-mode wrapper) |
| `mcEstimate_mse` | closed (term-mode wrapper) |
| `mcEstimate_consistent_ae` | closed |

The first three are literally the corresponding `*_avg_eval_pi` lemma:
`mcEstimate g` is definitionally `fun x => (n : ℝ)⁻¹ * ∑ i, g (x i)`, so no
`unfold` is required.  `mcEstimate_consistent_ae` transports the `Finset.range`
form of the SLLN through `Fin.sum_univ_eq_sum_range` inside a `Tendsto.congr`.

## Pre-existing issues left untouched (not obstructions)

The build emits two `linter.style.whitespace` warnings that are **not** caused by
this lane and cannot be fixed without editing frozen statements:

* `ForMathlib/PiMoments.lean:130:7`
* `MonteCarlo/Estimation.lean:77:7`

Both are the alignment of the `-- LEAN-ONLY: measurability of the integrand`
comment line inside the frozen signature of `tendsto_avg_eval_infinitePi` /
`mcEstimate_consistent_ae`.  They were present verbatim at the stub gate before
any proof work (confirmed by the baseline `lake build` at the start of this
session).  Hard rule 1 forbids touching the signature, so they are left as-is;
a docstring-surface owner should fix them.

## Gate output (foreground `lake build`, tail)

```
⚠ [2626/2627] Replayed StatLean.ComputationalStatistics.ForMathlib.PiMoments
warning: StatLean/ComputationalStatistics/ForMathlib/PiMoments.lean:130:7: extra space in the source

This part of the code
  '(hg : Integrable'
should be written as
  '(hgm : Measurable'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
⚠ [2627/2627] Built StatLean.ComputationalStatistics.MonteCarlo.Estimation (18s)
warning: StatLean/ComputationalStatistics/MonteCarlo/Estimation.lean:77:7: extra space in the source

This part of the code
  '(hg : Integrable'
should be written as
  '(hgm : Measurable'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
Build completed successfully (2627 jobs).
```

Final sorry count of the touch-set: **0** (`PiMoments.lean` 0,
`Core/EmpiricalMeasure.lean` 0, `MonteCarlo/Estimation.lean` 0).
