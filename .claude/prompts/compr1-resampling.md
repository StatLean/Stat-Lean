# Lane C — comp/r1-resampling: PiMarginal + counts bridge + moments + particle/bootstrap

READ `.claude/prompts/compr1-_common.md` FIRST and obey every shared rule.

## Touch-set (the ONLY files you may modify)

1. `StatLean/ComputationalStatistics/ForMathlib/PiMarginal.lean`
2. `StatLean/ComputationalStatistics/Resampling/CategoricalCounts.lean`
3. `StatLean/ComputationalStatistics/Resampling/MultinomialMoments.lean`
4. `StatLean/ComputationalStatistics/Resampling/ParticleResampling.lean`
5. `StatLean/ComputationalStatistics/Resampling/BootstrapMoments.lean`
(+ `LANE-REPORT.md`)

Build gate: `lake build` of those five modules (list them all on one line).

You may USE (compiling, possibly still sorried): everything in
`Core/EmpiricalMeasure.lean` (`integral_empiricalMeasure`, `integral_categorical`,
`isProbabilityMeasure_categorical`, `weightedMeasure_eq_map_categorical`,
`empiricalMeasure_eq_map_categorical`, `empiricalMeasure_apply`, …) and in
`ForMathlib/PiMoments.lean` (`integral_avg_eval_pi`, `variance_avg_eval_pi`).
Also `StatLean.Bayesian.multinomialWeight/multinomialKernel` API from
`StatLean/Bayesian/ForMathlib/MultinomialDist.lean` (READ that file first —
`multinomialKernel_apply_singleton` is your interface; do not modify it).

## Recommended order

PiMarginal → CategoricalCounts → ParticleResampling → BootstrapMoments →
MultinomialMoments. (The counts bridge `map_categoricalCounts_pi` is the
hardest single target of the whole batch — time-box it at 60 min, twice the
usual cap, and if it resists, close everything else first and return.)

## Targets and proof sketches

### PiMarginal

- `pi_map_deleteSplit`: Mathlib has the measurable equiv
  `MeasurableEquiv.piFinSuccAbove` with `x ↦ (x i, x ∘ i.succAbove)` (check the
  exact component order in the pin!) and a `Measure.pi` measure-preservation
  lemma for it — search `piFinSuccAbove` in
  `Mathlib/MeasureTheory/Constructions/Pi.lean` (e.g.
  `measurePreserving_piFinSuccAbove (μ) (i)` mapping `Measure.pi μ` to
  `(μ i).prod (Measure.pi (μ ∘ i.succAbove))`). With the constant family the
  composite is exactly the goal (`MeasurePreserving.map_eq`).
- `pi_map_precomp_succAbove`: compose the previous with `Prod.snd`:
  `Measure.map_map` (mind the direction — forward collapses) and
  `Measure.snd_prod` (`snd` marginal of a product with probability first
  factor; search `Measure.snd_prod` / `Measure.map_snd_prod`).

### CategoricalCounts

- `sum_categoricalCounts`: `∑ j, #{i | a i = j} = n` — partition of `univ` by
  fiber: `Finset.card_eq_sum_card_fiberwise` (or `Finset.sum_fiberwise_card`).
- `measurable_categoricalCounts`: `Measurable.of_discrete` — `Fin n → Fin m`
  is a finite discrete measurable space (instances: `Pi` of
  `MeasurableSingletonClass` over countable — if `of_discrete` does not fire
  because the pi-instance is not `DiscreteMeasurableSpace`, use
  `measurable_pi_lambda` + `measurable_to_countable`-style lemmas; on a finite
  domain every function into ℕ is measurable via
  `measurable_from_prod…` — simplest: `measurable_pi_lambda _ fun j =>
  measurable_from_top`? Check what fires; `Measurable.of_discrete` should).
- `map_categoricalCounts_pi` (HARD): both sides are finite measures on the
  countable discrete space `Fin m → ℕ`. Strategy: `Measure.ext`; reduce to
  singletons — on a countable `MeasurableSingletonClass` space two measures
  agree iff they agree on singletons (search `Measure.ext_iff_singleton`; it
  exists for σ-finite/counting-representable measures — otherwise write `s` as
  a countable union of its singletons via `Set.biUnion_of_singleton` +
  `measure_biUnion` disjoint-countable).
  RHS singleton: `multinomialKernel_apply_singleton` + `multinomialWeight`
  definition unfold: on-simplex, mass of `{v}` is
  `ofReal (Nat.multinomial univ v * ∏ j, q j ^ v j)` if `∑ v = n`, else `0`.
  LHS singleton: `Measure.map_apply measurable_categoricalCounts` →
  `(Measure.pi …) {a | categoricalCounts a = v}`. The fiber is a finite set in
  a finite space: its pi-measure is `∑_{a ∈ fiber} ∏ i, categorical q {a i}`
  (measure of a finite set = sum of singleton masses;
  `Measure.pi` singleton = `∏ i, (categorical q) {a i}` via `Measure.pi_pi`
  on the box `Set.pi univ (fun i => {a i})` = `{a}` — search
  `Set.univ_pi_singleton`). Each product `= ∏ j, (ofReal (q j)) ^ (v j)`
  (regroup the product over `i` by the fiber of `a` at each `j`:
  `Finset.prod_fiberwise` + `categorical_apply`-singleton — prove a small
  private lemma `(categorical q) {j} = ENNReal.ofReal (q j)`).
  So LHS `= (#fiber) • ∏ j (ofReal (q j))^(v j)`, and the counting fact is
  `#{a : Fin n → Fin m | ∀ j, #(a⁻¹ j) = v j} = Nat.multinomial univ v` when
  `∑ v = n` (and the fiber is empty otherwise, matching the junk-0).
  For the counting fact: search Mathlib for `multinomial` + `card`
  (`Nat.multinomial` in `Mathlib/Data/Nat/Choose/Multinomial.lean`; a
  cardinality bridge may exist via `Finset.card_piAntidiag` or the
  `Multiset.multinomial` API; also try `Fintype.card_of…`, and the
  `Finset.prod_pow_eq_pow_sum`-adjacent combinatorics). If no ready-made count
  exists, prove it by induction on `n` with `Fin.cons`-decomposition and the
  Pascal-style recurrence `Nat.multinomial` satisfies
  (`Nat.multinomial_succ`-search; the recurrence over decrementing one
  coordinate of `v`). This is legitimate ForMathlib-grade work; keep it as a
  same-file `private` lemma. Convert `ofReal (∏ …)` vs `∏ ofReal` with
  `ENNReal.ofReal_prod_of_nonneg`, powers with `ENNReal.ofReal_pow (hq0 j)`.

### ParticleResampling

- `particleResampling_unbiased`: `mcEstimate g (x ∘ a)` is the coordinate
  average of `g ∘ x : Fin m → ℝ` — apply `integral_avg_eval_pi` at
  `P := categorical w` (probability by `isProbabilityMeasure_categorical`),
  `g := g ∘ x`; integrability is free on a finite measure space with a
  function of finitely many values (`Integrable.of_finite` — search
  `Integrable.of_finite` / `integrable_of_fintype`), then
  `integral_categorical (g ∘ x) hw0` gives `∑ i, w i * g (x i)`.
- `particleResampling_unbiased_integral`: previous + `integral_weightedMeasure`.
- `particleResampling_measure_unbiased`: pointwise
  `(empiricalMeasure (x ∘ a) s).toReal = mcEstimate (Set.indicator s 1) (x ∘ a)`
  — via `empiricalMeasure_apply` and counting (`toReal` of
  `(N)⁻¹ * card = (N:ℝ)⁻¹ * card`), or via `lintegral`/`integral` of the
  indicator (`integral_empiricalMeasure` at the indicator, which is strongly
  measurable by `hs`). Then apply `particleResampling_unbiased` at the
  indicator and identify the RHS with `(weightedMeasure w x s).toReal`
  (expand `weightedMeasure` on `s`: `Measure.smul/sum/dirac_apply' _ hs` —
  `∑ i, w i * indicator = ∑ᵢ w i · 1[xᵢ ∈ s]`, and
  `ENNReal.toReal` of `∑ ofReal (w i) * 1[…]`).

### BootstrapMoments

- `bootstrap_linearStatistic_expectation`: `integral_avg_eval_pi` at
  `P := empiricalMeasure x` + `integral_empiricalMeasure hf` (integrability
  over the empirical measure: finite-measure + `Integrable.of_finite`? The
  empirical measure is NOT on a finite space — build `Integrable g
  (empiricalMeasure x)` from boundedness on the finite support: easiest via
  `integrable_smul_measure` + `integrable_finset_sum_measure` +
  `integrable_dirac`-style lemmas — search `MeasureTheory.integrable_dirac`,
  `Integrable.smul_measure`, and sum-measure integrability
  `MeasureTheory.integrable_finset_sum_measure`).
- `variance_empiricalMeasure`: `variance g (empiricalMeasure x)` — use
  `variance_eq_integral` (or `variance_def'`) + `integral_empiricalMeasure`
  twice (for `g` and for `(g - mean)²` — the latter is strongly measurable
  from `hg`), landing on
  `(n)⁻¹ ∑ (g(xᵢ) − mcEstimate g x)²`.
- `bootstrap_linearStatistic_variance`: `variance_avg_eval_pi` at
  `P := empiricalMeasure x` (`MemLp g 2` over a finitely-supported probability
  measure — from `hg` + boundedness on the support; search
  `memLp_of_bounded` or build via `MemLp.of_bound`) + previous. Algebra:
  `((1/n)·Σ)/n = (1/n²)·Σ` (`div` vs `(n^2)⁻¹`: `sq`, `mul_inv`, `ring`-able
  after `field_simp` with `(n:ℝ) ≠ 0`).
- `bootstrapMean_expectation` / `bootstrapMean_variance`: instances at
  `g = id` (`id` is strongly measurable: `stronglyMeasurable_id`).
- `bootstrapSqMean_expectation`: `E[Z²] = Var Z + (E Z)²` for
  `Z := mcEstimate id` (search `variance_add_sq_integral`-shaped lemma, or
  expand `variance_eq_integral` and rearrange); plug the two previous results.
- `bootstrapBiasCorrection_sqMean`: pure algebra from the previous target
  (`linarith`/`ring_nf` after rewriting).
- `resampleLaw_eq_map_indexResampling`: rewrite each factor by
  `empiricalMeasure_eq_map_categorical`, then `Measure.pi_map_pi` (pushforward
  of `Measure.pi` under coordinatewise maps `fun a i => x (a i)` — mind that
  our map is `fun a => x ∘ a`, the same function; `Function.comp` unfold).
- `bootstrapCounts_multinomial`: `map_categoricalCounts_pi` at
  `q := fun _ => (n:ℝ)⁻¹` (simplex side conditions: `inv_nonneg`,
  `Finset.sum_const` + `mul_inv_cancel₀` with `(n:ℝ) ≠ 0` from `NeZero`).

### MultinomialMoments

- Represent `(categoricalCounts a j : ℝ) = ∑ i, if a i = j then (1:ℝ) else 0`
  (`Finset.card_filter` + `Nat.cast_sum`; make it a same-file `private` lemma).
- `integral_categoricalCount`: linearity (`integral_finset_sum`) + each
  indicator integrates to `q j` via `measurePreserving_eval` +
  `(categorical q) {j} = ofReal (q j)` → `toReal = q j`.
  (Integral of an indicator of a singleton = measure of preimage; simplest:
  `∫ 1{a i = j}` over the pi measure = `(categorical q) {j}`.toReal.)
- `variance_categoricalCount`: `IndepFun.variance_sum` on the indicator family
  (independent by `iIndepFun_pi` with `X i := fun s => if s = j then 1 else 0`;
  `MemLp` free — bounded), each summand is a Bernoulli(`q j`) variance
  `q j * (1 - q j)` (compute via `variance_eq_integral`: indicator² =
  indicator, so `Var = q − q²`; needs `q j ≤ 1` — DERIVE it from `hq0 + hq1`:
  `q j = 1 − ∑_{k≠j} q k ≤ 1` — do not add a hypothesis).
- `covariance_categoricalCount`: bilinearity of `covariance` over the two
  finite sums (search `covariance_sum_left/right` / `covariance_fun_add` in
  `Mathlib/Probability/Moments/Covariance.lean` — READ that file's API first);
  cross-pairs (different coordinates) vanish:
  `IndepFun.covariance_eq_zero`-shaped lemma (independent coordinate
  indicators); same-coordinate pair: `Cov(1{s=j}, 1{s=k}) = E[1{s=j}1{s=k}]
  − q_j·q_k = 0 − q_j q_k` (`j ≠ k` makes the product indicator `0`).
  Total: `n` same-coordinate terms `= −n q_j q_k`.
