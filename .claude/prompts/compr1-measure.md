# Lane B — comp/r1-measure: importance sampling + rejection sampling

READ `.claude/prompts/compr1-_common.md` FIRST and obey every shared rule.

## Touch-set (the ONLY files you may modify)

1. `StatLean/ComputationalStatistics/MonteCarlo/ImportanceSampling.lean`
2. `StatLean/ComputationalStatistics/MonteCarlo/RejectionSampling.lean`
(+ `LANE-REPORT.md`)

Build gate: `lake build StatLean.ComputationalStatistics.MonteCarlo.ImportanceSampling
StatLean.ComputationalStatistics.MonteCarlo.RejectionSampling`

You may USE (they compile, some still sorried — that is fine): the PiMoments
lemmas `integral_avg_eval_pi`, `variance_avg_eval_pi` from
`StatLean.ComputationalStatistics.ForMathlib.PiMoments`.

## Targets and proof sketches

### ImportanceSampling

- `integral_importanceWeight_mul`: unfold `importanceWeight`; this is
  `MeasureTheory.integral_toReal_rnDeriv_mul hPQ` up to `mul_comm` inside the
  integrand (`simp only [mul_comm]` or `integral_congr_ae`).
- `importanceSampling_unbiased`: `mcEstimate` unfolds to the coordinate
  average; apply `integral_avg_eval_pi` at `g·w` (needs `[NeZero n]`, given),
  then the identity above.
- `importanceSampling_variance`: `variance_avg_eval_pi` at `g·w`.
- `lintegral_sq_le_lintegral_sq_div` (Cauchy–Schwarz in ℝ≥0∞):
  Case split on `E := {z | p z = 0 ∧ f z ≠ 0}`.
  If `ν E ≠ 0`: on `E` the integrand `f²/p = f²/0 = ∞` (`ENNReal.div_zero` needs
  `f² ≠ 0`), so the RHS is `∞` (`lintegral` over a positive-measure set where the
  integrand is `∞` — search `lintegral_eq_top_of…` or bound below by
  `∞ * ν E` via `setLIntegral`), and the bound is trivial (`le_top`).
  If `ν E = 0`: a.e. `f = (f / p ^ (1/2 : ℝ)) * p ^ (1/2 : ℝ)` — check the three
  pointwise cases (`p = 0 → f = 0`; `0 < p < ∞`; `p = ∞` gives `f/∞·∞`… handle
  `p = ∞` inside the a.e. by noting `∫⁻ p = 1` forces `p < ∞` a.e.,
  `ae_lt_top hp hp1.ne`). Then ℝ≥0∞ Cauchy–Schwarz:
  `ENNReal.lintegral_mul_le_Lp_mul_Lq` (Hölder with `p = q = 2`; search the
  exact name in `Mathlib/Analysis/MeanInequalities*` — the lintegral Hölder is
  `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `Real.HolderConjugate` or
  `.IsConjExponent`), giving `∫f ≤ (∫ f²/p)^(1/2) * (∫ p)^(1/2)`; square both
  sides (`ENNReal.rpow`-algebra; `hp1` kills the second factor).
  NOTE `f z ^ 2 / p z` vs `(f/√p)²`: `ENNReal.div_pow`, `ENNReal.rpow`-to-`pow`
  bridges (`ENNReal.rpow_natCast`, `ENNReal.rpow_two`); alternatively run the
  whole proof with `a := f * (p ^ (2⁻¹ : ℝ))⁻¹`-free formulations. If the rpow
  juggling stalls, an alternative route: apply the general
  `lintegral_mul_le_lintegral_sq_mul_lintegral_sq`-style inner-product CS if
  present, or prove via `ENNReal.lintegral_rpow…`. Time-box and report if truly
  stuck.
- `lintegral_sq_div_optimalImportance`: set `c := ∫⁻ f ∂ν`; three cases.
  `c = 0`: `f = 0` a.e. (`lintegral_eq_zero_iff hf`), integrand a.e. `0`
  (`0^2 / (0/0) = 0/0 = 0`), both sides `0`.
  `c = ∞`: `f/∞ = 0` pointwise (`ENNReal.div_top`), integrand `= f²/0 = ∞` on
  `{f ≠ 0}` which has positive measure (else `c = 0`), so LHS `= ∞ = c²`.
  `0 < c < ∞`: pointwise a.e. `f² / (f/c) = f * c` — cases `f z = 0` (both `0`);
  `0 < f z < ∞` (`ENNReal.div_div_eq_mul_div`-style algebra:
  `f²/(f/c) = f²*c/f = f*c`, use `ENNReal.div_eq_mul_inv`,
  `ENNReal.mul_inv` with the finiteness side conditions, or
  `ENNReal.eq_div_iff`-style cross-multiplication); `f z = ∞` is a.e. excluded
  (`ae_lt_top hf` fails since `c < ∞` gives `f < ∞` a.e.).
  Then `∫⁻ f*c = c * c` by `lintegral_mul_const'` (`c ≠ ∞`).

### RejectionSampling

- `isProbabilityMeasure_uniform01`: `Measure.restrict_apply_univ` +
  `Real.volume_Icc`; `⟨by simp [uniform01, Real.volume_Icc]⟩`.
- `measurableSet_rejectionAccept`: the set is
  `{yu | φ yu ≤ ψ yu}` for the measurable functions
  `φ (y,u) = ENNReal.ofReal u * (c * q y)` and `ψ (y,u) = p y`:
  `measurableSet_le` + product-measurability (`ENNReal.measurable_ofReal.comp
  measurable_snd`, `hq.comp measurable_fst`, etc.).
- `rejectionSampling_restrict_map` (the workhorse): prove measure equality by
  `Measure.ext fun S hS`. LHS via `Measure.map_apply measurable_fst hS`, then
  `Measure.restrict_apply` and `Measure.prod_apply` (the section of
  `rejectionAccept ∩ (S ×ˢ univ)` at `y ∈ S` is
  `{u | ENNReal.ofReal u * (c * q y) ≤ p y}`).
  Key inner computation, for ν-a.e. `y` (work under the a.e. filter of
  `ν.withDensity q`, whose null sets include `{q = 0}` intersected sets — or
  directly under `∫⁻ … q dν` after `lintegral_withDensity_eq_lintegral_mul`):
  when `0 < c * q y < ∞`, `uniform01 {u | ofReal u ≤ p y / (c*q y)}` — rewrite
  the constraint as `u ≤ (p y / (c*q y)).toReal` (envelope gives ratio ≤ 1) —
  `= p y / (c * q y)` (compute `volume (Icc 0 1 ∩ Iic t) = ofReal t` for
  `t ∈ [0,1]`).
  Cases `q y = 0` (then `p y = 0` by envelope + `hc0`… careful: envelope gives
  `p y ≤ c * 0 = 0`): accept-section is `univ`, but the `withDensity q` weight
  is `0`, so the discrepancy `1 ≠ 0/0` is killed by the density factor —
  organize the computation as
  `∫⁻ y in S, uniform01(section y) * q y ∂ν` and show the integrand
  `= p y / c` for EVERY `y` with the case analysis (`q y = 0 → p y = 0 →` both
  sides `0`; `q y = ∞` handled by `c ≠ 0` making the section `{u ≤ 0}`-null or
  by a.e.-finiteness of `q` if you add nothing — prefer the pointwise case
  split, `ENNReal.div_mul_cancel`-style: `(p y / (c * q y)) * q y = p y / c`
  needs `q y ≠ 0, ≠ ∞`; at `q y = ∞` with `p y` finite the section measure is
  `0` unless `p y = ∞`… if this corner resists a pointwise identity, restrict
  to the a.e.-finiteness set: `q < ∞` a.e.[ν] is NOT given — handle `q y = ∞`:
  section `{u | ofReal u * ∞ ≤ p y}` = `{u ≤ 0}` when `p y < ∞` (null under
  uniform01 up to the point 0 — `ofReal 0 * ∞ = 0 * ∞ = 0 ≤ p y` so `u = 0`
  IS accepted; the section is `Iic 0`-like, uniform01-measure 0), and
  `p y = ∞` contradicts envelope-with-`c ≠ ∞` only if `q y` finite — at
  `q y = ∞`, `p y = ∞` allowed: section = univ, integrand `1 * ∞ = ∞`;
  RHS `p y / c = ∞`. Check it matches.)
  Then `∫⁻ y in S, p y / c ∂ν = c⁻¹ * ∫⁻ y in S, p y ∂ν
  = (c⁻¹ • ν.withDensity p) S` (`div_eq_mul_inv`, `lintegral_const_mul'`,
  `withDensity_apply _ hS`, `Measure.smul_apply`).
- `rejectionSampling_acceptProb`: instantiate the ext-computation at
  `S = univ` — or `map_apply` at `univ`: acceptance mass = (restrict…map) univ
  `= (c⁻¹ • ν.withDensity p) univ = c⁻¹ * 1` by `hp1` and
  `withDensity_apply_univ`-style lemma (`lintegral` form).
- `rejectionSampling_conditionalLaw`: `ProbabilityTheory.cond` unfolds to
  `(μ A)⁻¹ • μ.restrict A` (search `ProbabilityTheory.cond` def /
  `cond_apply`). `Measure.map_smul` + the two previous targets:
  `(c⁻¹)⁻¹ • (c⁻¹ • ν.withDensity p) = ν.withDensity p` by `smul_smul`,
  `ENNReal.inv_inv`, `ENNReal.mul_inv_cancel hc0 hcT`… careful with the order:
  `(c⁻¹)⁻¹ * c⁻¹ = c * c⁻¹ = 1`.
