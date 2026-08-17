# Lane A — comp/r1-core: PiMoments + EmpiricalMeasure + Monte Carlo estimation

READ `.claude/prompts/compr1-_common.md` FIRST and obey every shared rule.

## Touch-set (the ONLY files you may modify)

1. `StatLean/ComputationalStatistics/ForMathlib/PiMoments.lean`
2. `StatLean/ComputationalStatistics/Core/EmpiricalMeasure.lean`
3. `StatLean/ComputationalStatistics/MonteCarlo/Estimation.lean`
(+ `LANE-REPORT.md`)

Build gate: `lake build StatLean.ComputationalStatistics.ForMathlib.PiMoments
StatLean.ComputationalStatistics.Core.EmpiricalMeasure
StatLean.ComputationalStatistics.MonteCarlo.Estimation`

## Targets and proof sketches

### PiMoments (do these first — Estimation wraps them)

- `integral_avg_eval_pi`: pull the constant out (`integral_const_mul` after
  `integral_finset_sum`), each `∫ x, g (x i) ∂(Measure.pi …) = ∫ g dP` by
  `(MeasureTheory.measurePreserving_eval _ i).integral_comp` (or `map_eq` +
  `integral_map`); then `(n)⁻¹ * (n * ∫g) = ∫g` via `NeZero`.
  Integrability of `g ∘ eval i` transports along the same measure-preservation.
- `variance_avg_eval_pi`: `variance_smul`-style constant extraction
  (`variance` of `c * X` is `c^2 * variance X` — search `variance_const_mul` /
  `variance_smul`), then `ProbabilityTheory.IndepFun.variance_sum` with the
  family `fun i x => g (x i)`: independence is `ProbabilityTheory.iIndepFun_pi`
  (constant family `X i := g`), `MemLp` of each summand transports along
  `measurePreserving_eval` (search `MeasurePreserving.memLp_comp` or use
  `MemLp.comp_measurePreserving`). Each variance equals `variance g P` (variance
  is invariant under measure-preserving pushforward — search
  `variance_map`). Final algebra: `(n⁻¹)^2 * n * σ² = σ²/n`.
- `integral_sq_dev_avg_eval_pi`: show the LHS *is* the variance of the average
  (the average's mean is `∫ g dP` by the first target; use `variance_eq_integral`
  or `variance` characterization `variance X μ = ∫ (X - ∫X)²` — search
  `variance_eq_integral`, needs an `AEMeasurable`/`MemLp` side condition), then
  apply the previous target.
- `tendsto_avg_eval_infinitePi`: apply `ProbabilityTheory.strong_law_ae_real`
  to `X i ω := g (ω i)` over `Measure.infinitePi (fun _ : ℕ => P)`.
  Ingredients: (a) pairwise independence — get `iIndepFun` of the coordinates
  under `infinitePi` (search `iIndepFun` in `Mathlib/Probability/ProductMeasure.lean`;
  if only finite-marginal lemmas exist, derive via `Measure.infinitePi_pi` and
  the kernel-free characterization `iIndepFun_iff…`; a route via
  `IsProjectiveLimit` also works), then `.comp` with `g` and `.pairwise`;
  (b) identical distribution — each coordinate has law `P` (search
  `infinitePi_map_eval` or derive from `Measure.infinitePi_pi` on cylinder sets),
  package as `IdentDistrib` via equal laws (`IdentDistrib` of equal `Measure.map`s);
  (c) integrability of `X 0` — transport `hg` along the law.
  Then rewrite `strong_law_ae_real`'s `(∑ i ∈ range n, X i ω) / n` into
  `(n)⁻¹ * ∑ i ∈ range n, g (ω i)` by `div_eq_inv_mul`.

### Core/EmpiricalMeasure

- `isProbabilityMeasure_empiricalMeasure`: `measure_univ`: `smul_apply` +
  `Measure.finset_sum_apply` (search `Measure.coe_finset_sum` /
  `Measure.sum_apply`) + `Measure.dirac_apply_of_mem` → `(n)⁻¹ * n = 1` by
  `ENNReal.inv_mul_cancel` (`Nat.cast_ne_zero` from `NeZero`, `natCast_ne_top`).
- `empiricalMeasure_apply`: same expansion; `dirac_apply' _ hs` gives indicator;
  sum of indicators over `Fin n` = filter card (`Finset.sum_boole` /
  `Finset.card_filter`).
- `integral_empiricalMeasure`: `integral_smul_measure` +
  `integral_finset_sum_measure` + `integral_dirac' _ _ hf`; then
  `ENNReal.toReal_inv`/`toReal_natCast` to land on `mcEstimate` (unfold it).
- `lintegral_empiricalMeasure`: `lintegral_smul_measure` +
  `lintegral_finset_sum_measure`(search exact name) + `lintegral_dirac' _ hφ`.
- `isProbabilityMeasure_weightedMeasure`: univ mass `∑ ofReal (w i)` =
  `ofReal (∑ w) = 1` via `ENNReal.ofReal_sum_of_nonneg hw0`, `hw1`.
- `integral_weightedMeasure`: sum + smul + dirac as above;
  `(ENNReal.ofReal (w i)).toReal = w i` by `ENNReal.toReal_ofReal (hw0 i)`.
- `empiricalMeasure_eq_weightedMeasure`: measure ext or direct rewriting:
  `ENNReal.ofReal (n:ℝ)⁻¹ = (n : ℝ≥0∞)⁻¹` (search `ENNReal.ofReal_inv_of_pos`,
  `ENNReal.ofReal_natCast`), then `Finset.smul_sum` to move the constant in/out.
- `integral_categorical` / `isProbabilityMeasure_categorical`: identical to the
  weighted case at `x = id` (use `categorical_eq_weightedMeasure`).
- `weightedMeasure_eq_map_categorical`: `Measure.map` is linear:
  `Measure.map_smul`, map of a finite sum (search `Measure.map_add` /
  `Measure.map_finset_sum`), `Measure.map_dirac (Measurable.of_discrete)` sends
  `dirac i ↦ dirac (x i)`.
- `empiricalMeasure_eq_map_categorical`: chain the previous two lemmas.

### MonteCarlo/Estimation

All four are wrappers: `unfold mcEstimate` (or `simp only [mcEstimate]`) and
apply the corresponding PiMoments lemma. For `mcEstimate_consistent_ae`, the
PiMoments SLLN is in `range`-sum form: rewrite with `Fin.sum_univ_eq_sum_range`.
