# bayes4-tests — Lemma 10.3: exponentially powerful tests [wave 1]

Branch `bay/bvm-tests`. The shared rules above apply.

## Touch-set (ONLY these files)

- `StatLean/Bayesian/BernsteinVonMises/ScoreTest.lean`
- `StatLean/Bayesian/BernsteinVonMises/TestBoost.lean`
- `StatLean/Bayesian/BernsteinVonMises/ExponentialTests.lean`

Gate: `lake build StatLean.Bayesian.BernsteinVonMises.ExponentialTests`

Provided 0-sorry (verified on the pin — reuse, do not reprove):
- DQM toolbox `StatLean/AsymptoticStatistics/DQM/Properties.lean`:
  `dqm_sqrt_density_l2_convergence`, `dqm_score_memLp_two`, `dqm_fisher_integrable`,
  `dqm_fisher_cont`, `dqm_residual_eventually_memLp` (namespace `AsymptoticStatistics`);
  `M.sqrtDensity_sq`, `M.sqrtDensity_memLp_two` (`ParametricFamily/Defs.lean`).
- `StatLean.ConcentrationInequalities.hoeffding`
  (`ConcentrationInequalities/SubGaussian/Hoeffding.lean:119`): one-sided tail
  `μ.real {ω | n·t ≤ ∑_{i<n} (X i ω − E X i)} ≤ exp(−n t²/(2σ²))` for `iIndepFun X μ`,
  `IsSubGaussian (X i) σ² μ`; and `isSubGaussian_of_mem_Icc`
  (`…/SubGaussian/Bounded.lean`) for bounded variables.
- `ProbabilityTheory.iIndepFun_pi` (`Mathlib/Probability/Independence/Basic.lean`):
  coordinates of `Measure.pi` are `iIndepFun`; compose per-coordinate functions with
  `iIndepFun.comp`. `AsymptoticRepresentation.productMeasure` IS `Measure.pi` of
  `μ.withDensity (ofReal ∘ density θ)` definitionally.
- `MeasureTheory.measurePreserving_eval` for per-coordinate laws under `Measure.pi`.
- Chebyshev: `MeasureTheory.meas_ge_le_lintegral_div` or `ProbabilityTheory.meas_ge_le_variance_div_sq`
  (check exact pin name with loogle '"variance_div"').

## Per-file targets

### ScoreTest.lean
- `measurable_bvmTruncScore`: coordinatewise `max/min` of measurable coordinates through
  `WithLp.equiv` (`measurable_pi_lambda`, `(WithLp.equiv _ _).symm` is measurable — it is
  the identity on the underlying type; `PiLp` measurability via `measurable_pi_apply`).
- `norm_bvmTruncScore_le`: `EuclideanSpace.norm_eq` (`√(∑ xᵢ²)`), each `|clamp| ≤ L`,
  `∑ ≤ k L²`, `Real.sqrt_le_sqrt` + `Real.sqrt_mul_self`.
- `truncScore_mean_expansion` — THE HARD TARGET (vdV p. 143). Route: write
  `∫ f^L d(P_θ − P_{θ₀}) = ∫ f^L (√p_θ − √p_{θ₀})(√p_θ + √p_{θ₀}) dμ` coordinatewise; DQM
  gives `√p_θ − √p_{θ₀} = ½⟪θ−θ₀, sc⟫√p_{θ₀} + r_θ` with `‖r_θ‖_{L²} = o(‖θ−θ₀‖)`
  (this is `hDQM.mem` + `hDQM.isLittleO` — unfold `DifferentiableQuadraticMean`);
  expand the product; the main term gives `∫ ⟪θ−θ₀, sc⟫ f^L p_{θ₀}` after
  `(√p_θ + √p_{θ₀}) = 2√p_{θ₀} + (√p_θ − √p_{θ₀})`; cross terms are `o(‖θ−θ₀‖)` by
  Cauchy–Schwarz (`MeasureTheory.lintegral_mul_le_Lp_mul_Lq` or
  `inner_mul_le_norm_mul_norm` on L²) with `f^L` bounded and
  `dqm_sqrt_density_l2_convergence` for `‖√p_θ − √p_{θ₀}‖_{L²} = O(‖θ−θ₀‖)`.
  Work component-by-component (`EuclideanSpace` coordinates) to stay scalar. Sanctioned
  NAMED DEBT if it resists after a serious attempt (~45 min): isolate exactly this lemma.
- `truncScore_separation`: dominated convergence in `L`:
  `∫ ⟪u, sc⟫ • f^L dP_{θ₀} → ∫ ⟪u, sc⟫ • sc dP_{θ₀}` coordinatewise as `L → ∞`
  (dominated by `‖sc‖²`-integrable, `dqm_fisher_integrable`); the limit matrix is `J` via
  `hJ`; `J` PosDef gives `⟪u, Ju⟫ ≥ λmin‖u‖²` (use
  `Matrix.PosDef....` smallest-eigenvalue bound, or avoid eigenvalues: continuity of
  `A ↦ inf_{‖u‖=1}⟪u,Au⟫` is overkill — pick `L` with the bilinear-form distance
  `< λ/2` where `λ := inf` over the unit sphere of `⟪u, Ju⟫`, positive by compactness +
  PosDef); combine with `truncScore_mean_expansion` (o-term `< c/2‖θ−θ₀‖` on a small ball).
- `truncScore_empirical_dev_tail`: per coordinate `j`, two applications of `hoeffding`
  (to `±X` where `X i ω := (f^L (ω i))_j`) under `productMeasure M μ θ n`; coordinates are
  `iIndepFun` by `iIndepFun_pi` + `iIndepFun.comp`; `IsSubGaussian` from
  `isSubGaussian_of_mem_Icc` with `[−L, L]` (σ² = L²; check the Icc-lemma's proxy —
  adapt constants: the STATED bound has `2k·exp(−n s²/(2 k L²))`; the union bound over
  `2k` one-sided events at per-coordinate threshold `s/√k` gives it).
- `exists_moderate_tests`: assemble — define the test as the indicator
  `bvmScoreTest`-style using `truncScore_separation`'s `(L, ε, c)`; threshold
  `√(Mseq n / n)`; Type I via Chebyshev (variance of the empirical mean is `O(1/n)`,
  threshold² is `Mseq n / n`, ratio `O(1/Mseq n) → 0`) — Markov on the squared norm is
  enough (`meas_ge_le_lintegral_div`); Type II: on `Mₙ/√n ≤ ‖θ−θ₀‖ ≤ ε`, separation gives
  mean displacement `≥ c‖θ−θ₀‖`, threshold is eventually `≤ c‖θ−θ₀‖/2`
  (since `√(Mₙ/n) ≤ (c/2)(Mₙ/√n) ≤ (c/2)‖θ−θ₀‖` eventually — needs `Mₙ → ∞`), then
  `truncScore_empirical_dev_tail` at `s := c‖θ−θ₀‖/2` under `P^n_θ`; absorb `2k` into the
  exponential constant (shrink `c`).

### TestBoost.lean
- `blockAvg_typeII_tail`: the block statistics `Y_j(ω) := g (block j of ω)` are
  `iIndepFun` under `productMeasure M μ θ n` (disjoint coordinate blocks:
  `iIndepFun_pi` + composition with the block projections — the blocks use disjoint index
  sets, so independence follows from grouping; if the general grouping lemma is painful,
  use `iIndepFun.comp` after reindexing `Fin n ≃ Fin (n/kb) × Fin kb`-style on the
  product measure via `Measure.pi` reindexing — `MeasureTheory.measurePreserving_piCongrLeft`
  family); each `Y_j ∈ [0,1]` with mean `≥ 3/4`; `hoeffding` applied to `−Y` at `t = 1/4`
  over `m := n/kb` blocks gives `exp(−m·(1/4)²/(2·(1/4)-ish))` — the STATED bound is
  `exp(−m/8)`, which matches Hoeffding with range-[0,1] proxy `σ² = 1/4`:
  `exp(−m (1/4)²/(2·¼)) = exp(−m/8)`.
- `exists_boosted_tests`: pick `kb` from `hTests` at level `ε` with both errors `< 1/4`
  (the `∀ δ` clause at `δ := 1/4` + the Type-I tendsto); define `φ n` as the indicator
  `{bvmBlockAvg kb (φtests kb) n · ≥ 1/2}`; Type I at `θ₀`: block mean `≤ 1/4`, Hoeffding
  upper tail `≤ exp(−m/8) → 0`; Type II uniform over `ε ≤ ‖θ−θ₀‖`: `blockAvg_typeII_tail`;
  `c := 1/(16 kb)`-ish so `exp(−m/8) ≤ exp(−c n)` for `n ≥ 2 kb` (`m = ⌊n/kb⌋ ≥ n/(2kb)`).

### ExponentialTests.lean
- `exponential_tests`: `φ n := max (φmod n) (φfar n)` from `exists_moderate_tests` (with
  this `Mseq`) and `exists_boosted_tests` (at the `ε` returned by the moderate lemma);
  size: `∫ max ≤ ∫ φmod + ∫ φfar → 0`; power: case `‖θ−θ₀‖ ≤ ε` uses
  `1 − max ≤ 1 − φmod` and the moderate bound (`exp(−c n ‖θ−θ₀‖²)`; on this range
  `‖θ−θ₀‖² = min (‖θ−θ₀‖²) 1` once `ε ≤ 1` — shrink `ε` wlog); case `ε ≤ ‖θ−θ₀‖` uses
  the far bound `exp(−c_far n) ≤ exp(−c n · min (‖θ−θ₀‖²) 1)` with `c ≤ c_far` (since
  `min ≤ 1`). Take `c := min c_mod c_far` adjusted by `min(ε²,1)`; `IsExpConsistentTestSeq`
  fields assemble directly.

## Done

Gate green; per-target closed/left. Sanctioned NAMED DEBT (max 1):
`truncScore_mean_expansion`. Everything downstream of it in this lane must still be closed
(they consume its statement, not its proof).
