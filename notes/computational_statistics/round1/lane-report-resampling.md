# Lane C — `comp/r1-resampling`: LANE REPORT

**Status: all 17 targets closed. 0 sorries in the touch-set, 0 build errors.**

No obstructions found; every frozen statement was provable as stated. No
statement, hypothesis, docstring, or definition was modified — only `sorry`
bodies were filled, plus same-file `private` helpers and (in
`CategoricalCounts.lean`) one extra `open scoped Nat` for the `!` factorial
notation.

## Per-target status

### `ForMathlib/PiMarginal.lean` (2/2)

| target | status |
| --- | --- |
| `pi_map_deleteSplit` | **closed**, axiom-clean |
| `pi_map_precomp_succAbove` | **closed**, axiom-clean |

Both are the pinned `measurePreserving_piFinSuccAbove` at a constant family;
the deletion map is the `Prod.snd` marginal of the split (`Measure.map_map` +
`Measure.map_snd_prod` + `measure_univ`).  A `private` helper
(`map_deleteSplit_aux`) carries the content so that `pi_map_precomp_succAbove`,
which is stated *before* `pi_map_deleteSplit` in the frozen file, can use it
without reordering the declarations.

### `Resampling/CategoricalCounts.lean` (3/3)

| target | status |
| --- | --- |
| `sum_categoricalCounts` | **closed** |
| `measurable_categoricalCounts` | **closed** (`Measurable.of_discrete` fires) |
| `map_categoricalCounts_pi` | **closed**, axiom-clean |

The hard bridge went through in two halves.

*Combinatorial half.*  `Nat.multinomial` has **no** cardinality bridge in the
pin, so the counting fact was proved from scratch as a `private` lemma:
`#{a : Fin n → Fin m | counts a = v} = Nat.multinomial univ v` whenever
`∑ v = n`, by induction on `n`, peeling the first coordinate
(`Finset.card_eq_sum_card_fiberwise` on `a ↦ a 0`, then a `Finset.card_nbij'`
bijection with `Fin.cons`/`fun i => a i.succ` onto the fiber over
`Function.update v j (v j - 1)`).  The matching Pascal-style recurrence for
the coefficient itself,
`∑_{j : vⱼ ≠ 0} multinomial (update v j (vⱼ−1)) = multinomial v`, is *not* in
the pin either; it is proved by clearing the factorial denominators with
`Nat.multinomial_spec` and `Nat.mul_factorial_pred` (multiply through by
`∏ (vᵢ)!`, use `∏ (vᵢ)! = vⱼ · ∏ (update …)!`, and sum `∑ vⱼ · N! = (N+1)!`).
Both are `private` and ForMathlib-grade.

*Measure half.*  `Measure.ext_of_singleton` on the countable space `Fin m → ℕ`;
the left singleton mass is `Measure.tsum_indicator_apply_singleton` over the
finite fiber, each term `Measure.pi_pi` on `Set.univ_pi_singleton`, regrouped
by category with `Finset.prod_fiberwise_of_maps_to` into `∏ⱼ (ofReal qⱼ)^{vⱼ}`.
Off-simplex-support the fiber is empty (via `sum_categoricalCounts`), which
matches the junk `0` of `multinomialWeight` exactly — so the frozen simplex
hypotheses are used only for the on-support branch, as the stub docstring
predicted.

A `private instance isFiniteMeasure_categorical` was needed: `Measure.pi_pi`
demands `SigmaFinite` on the factors, and `categorical q` carries no such
instance for a general real `q`.

### `Resampling/ParticleResampling.lean` (3/3)

| target | status |
| --- | --- |
| `particleResampling_unbiased` | **closed** |
| `particleResampling_unbiased_integral` | **closed** |
| `particleResampling_measure_unbiased` | **closed** |

Exactly the sketched route: `integral_avg_eval_pi` at `P := categorical w`
(integrability free by `Integrable.of_finite` on the finite index space) then
`integral_categorical`.  The setwise form goes through the pointwise identity
`(𝔽_N(x∘a))(s).toReal = mcEstimate (s.indicator 1) (x∘a)` and closes against
`integral_indicator_one` on the weighted measure, so no direct expansion of
`weightedMeasure` on `s` was needed.

Non-blocking lint note: `particleResampling_unbiased` triggers
`linter.unusedSectionVars` for `[MeasurableSpace 𝓧]` — the proof never needs
it.  Silencing it would require `omit [MeasurableSpace 𝓧] in`, which *changes
the elaborated statement* (drops an instance argument), so it was deliberately
NOT done.

### `Resampling/BootstrapMoments.lean` (9/9)

| target | status |
| --- | --- |
| `bootstrap_linearStatistic_expectation` | **closed** |
| `variance_empiricalMeasure` | **closed** |
| `bootstrap_linearStatistic_variance` | **closed** |
| `bootstrapMean_expectation` | **closed** |
| `bootstrapMean_variance` | **closed** |
| `bootstrapSqMean_expectation` | **closed** |
| `bootstrapBiasCorrection_sqMean` | **closed** |
| `resampleLaw_eq_map_indexResampling` | **closed** |
| `bootstrapCounts_multinomial` | **closed**, axiom-clean |

Three `private` bricks carry the integrability side, all with **no growth
assumption on `g`**: `integrable_empiricalMeasure` (the empirical measure is
`c • ∑ dirac`, so `integrable_finset_sum_measure` + `integrable_dirac'` +
`Integrable.smul_measure`), `memLp_two_empiricalMeasure` (via
`memLp_two_iff_integrable_sq`), and `memLp_two_mcEstimate_id` (coordinate
maps are `MemLp 2` by `measurePreserving_eval` + `memLp_map_measure_iff`, then
`memLp_finset_sum` + `MemLp.const_mul`).  `bootstrapSqMean_expectation` is
`variance_eq_sub` at `mcEstimate id` fed by the two mean-case results.

Gotcha worth recording: in `bootstrap_linearStatistic_variance` one must *not*
`rw` an eta-expansion of `mcEstimate g` — the pattern also matches
`mcEstimate g x` on the right-hand side and silently unfolds the sample mean
there, leaving `ring` with two different normal forms.  Use a typed `have` for
`variance_avg_eval_pi` instead.

### `Resampling/MultinomialMoments.lean` (3/3)

| target | status |
| --- | --- |
| `integral_categoricalCount` | **closed** |
| `variance_categoricalCount` | **closed** |
| `covariance_categoricalCount` | **closed** |

Counts are rewritten as sums of coordinate indicators (`Finset.card_filter` +
`Nat.cast_sum`).  Independence is `iIndepFun_pi` applied at `X i = id`, giving
independence of the coordinate projections, then `IndepFun.comp` with the
indicator functions — this is more flexible than instantiating `iIndepFun_pi`
at the indicators themselves, because the covariance target needs *two
different* indicator functions (`1{· = j}` and `1{· = k}`).

Both second-moment targets are `variance_fun_sum` /
`covariance_fun_sum_fun_sum` on the double sum, with the off-diagonal killed by
`IndepFun.covariance_eq_zero` and the diagonal computed by
`covariance_eq_sub`.  **`q j ≤ 1` was never needed** — the derivation the
prompt anticipated (`q j = 1 − ∑_{k≠j} q k ≤ 1`) is unnecessary, since
`Var = qⱼ − qⱼ²` and `n·qⱼ·(1−qⱼ)` agree by `ring` without any bound.

## Axioms

`#print axioms` (scratch, since removed) reports only
`[propext, Classical.choice, Quot.sound]` for

* `pi_map_deleteSplit`, `pi_map_precomp_succAbove`,
* `map_categoricalCounts_pi`,
* `bootstrapCounts_multinomial`.

Every other target legitimately reports `sorryAx` because it routes through
still-sorried declarations of **other lanes' files** —
`Core/EmpiricalMeasure.lean` (`integral_empiricalMeasure`,
`integral_categorical`, `isProbabilityMeasure_categorical`,
`empiricalMeasure_apply`, `integral_weightedMeasure`,
`empiricalMeasure_eq_map_categorical`, …) and `ForMathlib/PiMoments.lean`
(`integral_avg_eval_pi`, `variance_avg_eval_pi`).  This is expected under the
batch rules; those lanes' closures will make these axiom-clean with no change
here.

## Build gate

```
✔ [2632/2634] Built StatLean.ComputationalStatistics.ForMathlib.PiMarginal (22s)
⚠ [2633/2634] Built StatLean.ComputationalStatistics.Resampling.MultinomialMoments (25s)
✔ [2634/2634] Built StatLean.ComputationalStatistics.Resampling.BootstrapMoments (26s)
Build completed successfully (2634 jobs).
```

0 errors.  Remaining warnings are cosmetic only: the pre-existing whitespace
lint in `ForMathlib/PiMoments.lean` (another lane's file), the
`unusedSectionVars` note above, and an `unusedVariables` note on the simplex
arguments of the `private` helper `memLp_two_pi` (they *are* consumed, by a
`haveI` instance the linter does not track).

Final sorry count of the touch-set: **0** (was 17).
