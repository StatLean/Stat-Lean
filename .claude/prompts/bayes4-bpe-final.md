# bayes4-bpe-final — Theorem 10.8 (Bayes point estimators) [wave 4]

Branch `bay/bpe-final`. The shared rules above apply.

## Touch-set (ONLY this file)

- `StatLean/Bayesian/BayesEstimators/Theorem10_8.lean`

Gate: `lake build StatLean.Bayesian.BayesEstimators.Theorem10_8`

Available on your base branch (closed in waves 1–3 — trust the statements):
- `posteriorRisk_shifted_majorant` (`UniformApproximation.lean`) — the τ-free measurable
  majorant `Mn` with `Mn →ᵖ 0` and, for `‖τ‖ ≤ R`, two-sided
  `|Zₙ(τ + Δₙ) − g(τ)| ≤ Mn`;
- `lintegral_loss_bvmGaussian` (same file) — `∫ ℓ(t−h) dN(Δₙ,J⁻¹) = g(t − Δₙ)`;
- `argmin_tendsto_of_uniform_approx` + `exists_gap_of_unique_argmin`
  (`ArgminConsistency.lean`) — deterministic argmin consistency;
- `posterior_tail_lintegral_tendsto` (10.9) (`PosteriorTails.lean`);
- `bernstein_von_mises` / `_lintegral` (`Theorem10_1.lean`), `scoreSum_uniformly_tight`;
- `gaussian_loss_convolution_continuous` / `_lt_top`
  (`AsymptoticStatistics/ForMathlib/MultivariateGaussianDensity.lean`);
- `AsymptoticStatistics.anderson_lemma_loss`
  (`ForMathlib/Anderson.lean:831`): `BowlShaped L` ⇒
  `∫⁻ L dN(0,S) ≤ ∫⁻ L(x + y) dN(0,S)` (`S.PosSemidef`);
  `AsymptoticStatistics.BowlShaped` fields: `measurable`, `symm : L (−x) = L x`,
  `convex_sublevel`.
- `AsymptoticRepresentation.scoreSum_weakly_converges` (score CLT) and
  `AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist`
  (`ForMathlib/Slutsky.lean`), `WeakConverges.map`.

## Targets

### `bpe_tight` (vdV Part 2, p. 148)
Let `δ := ` the radius from `hsep.strict` (there are `M, x, y` with `‖x‖ ≤ M`,
`2M ≤ ‖y‖`, `ℓ x < ℓ y`); set `η := ℓ y − ℓ x > 0` and `U := ball 0 M`.
For `‖t‖ ≥ 3Mₙ` (with `Mₙ → ∞` the (10.9) radii) and `h ∈ U`, `hsep.mono` gives
`ℓ(t − h) ≥ ℓ(−h)` and on the `U`-part a gain of `η`; the vdV display is
`Zₙ(t) − Zₙ(0) ≥ η·Post(U) − Post(ℓ(−·)·1_{C_nᶜ})`.
Formalize: split the posterior integral over `U`, `Uᶜ ∩ C_n`, `C_nᶜ`; on `U` use the
strict gap, on `Uᶜ ∩ C_n` use `hsep.mono` at scale `Mₙ` (nonneg difference), on `C_nᶜ`
bound below by `0` and subtract the (10.9) tail. Then:
- `Post(U) →_d N(X, J⁻¹)(U) > 0`: use `bernstein_von_mises` to compare `Post(U)` with
  `N(Δₙ,J⁻¹)(U)`, and `scoreSum_uniformly_tight` + the Gaussian lower bound
  `exists_pos_smul_volume_le_multivariateGaussian` (mean-uniform, on `‖Δₙ‖ ≤ K`) to get a
  deterministic `p₀ > 0` with `P{Post(U) ≥ p₀} → 1`.
- The tail term →ᵖ 0 by (10.9).
Conclude: `P{ 3Mₙ ≤ ‖√n(Tₙ−θ₀)‖ } → 0` because on the good event the minimizer cannot sit
outside (its criterion value would exceed `Zₙ(0) + εₙ`, contradicting `hT` at `t := 0`).
Convert `Mₙ → ∞` into the stated `∃ K` uniform-tightness form.

### `bayes_estimator_asymptotics` (headline)
Fix `ε > 0`. Let `Rₙ ω := √n(Tₙ ω − θ₀) − Δₙ ω`. Steps:
1. Tightness of `Rₙ`: from `bpe_tight` + `scoreSum_uniformly_tight` (`‖Rₙ‖ ≤ ‖√n(Tₙ−θ₀)‖ + ‖Δₙ‖`),
   giving `R` with `P{‖Rₙ‖ > R} ≤ ε'` eventually; enlarge `R` so `‖u₀‖ < R`
   (`u₀` is the unique argmin — `‖u₀‖ < ∞`).
2. `g := bpeGaussCriterion J ℓ` is continuous (`gaussian_loss_convolution_continuous`,
   `hJ_pd.inv`-PosDef: derive `(J⁻¹).PosDef` from `hJ_pd` — `Matrix.PosDef.inv`-style, check
   name) with unique minimizer `u₀` (`hunique`).
3. `Rₙ` is an approximate argmin of `zₙ(u) := Zₙ(u + Δₙ)` over `‖u‖ ≤ R`: from `hT` at
   `t := u + Δₙ` (note `√n(Tₙ−θ₀) = Rₙ + Δₙ`), with tolerance `εseq n`.
4. `zₙ` approximates `g` within `Mn` on the ball (`posteriorRisk_shifted_majorant`).
5. On the event `Gₙ := {‖Rₙ‖ ≤ R} ∩ {Mn ≤ γ}` (probability → 1 for any `γ > 0`), the
   deterministic lemma `argmin_tendsto_of_uniform_approx` applies **pointwise in ω** —
   but that lemma is stated for SEQUENCES. Use its ingredients instead: from
   `exists_gap_of_unique_argmin` get `η > 0`; for `γ` and `εseq n` small enough
   (`εseq n + 2γ < η`), the chain in that lemma's proof forces `‖Rₙ ω − u₀‖ < ρ` for every
   `ω ∈ Gₙ`. So directly: `P{ ε ≤ ‖Rₙ − u₀‖ } ≤ P(Gₙᶜ) → 0` with `ρ := ε`.
   (If you prefer, add a `private` pointwise version of the argmin lemma in this file and
   apply it to each `ω`.)

### `bayes_estimator_weakConverges`
`√n(Tₙ−θ₀) = Δₙ + (Rₙ − u₀) + u₀`; `Δₙ = toEuclideanCLM J⁻¹ (scoreSum)` has
`Δₙ ⇝ N(0, J⁻¹)` — from `scoreSum_weakly_converges` (`⇝ N(0,J)`) plus
`WeakConverges.map` under the CLM `toEuclideanCLM J⁻¹` and
`multivariateGaussian_map_toEuclideanCLM` (`J⁻¹ J (J⁻¹)ᴴ = J⁻¹`, as in the
`multivariateGaussian_map_matrix_inv` brick); then add the constant `u₀`
(`multivariateGaussian_map_const_add` + `WeakConverges.map`) and absorb `Rₙ − u₀ →ᵖ 0`
by `slutsky_of_tendstoInMeasure_dist` (convert the `.real`-form in-probability statement to
`TendstoInMeasure` as in `AsymptoticRepresentation.lean:1017`).

### `gaussCriterion_argmin_zero_of_bowlShaped`
`g(u) = ∫⁻ ℓ(u − z) dN(0,J⁻¹) = ∫⁻ ℓ(z − u) dN(0,J⁻¹)` (by `hL.symm` pointwise:
`ℓ(u−z) = ℓ(−(u−z)) = ℓ(z−u)`), `= ∫⁻ ℓ(z + (−u)) dN(0,J⁻¹) ≥ ∫⁻ ℓ z dN(0,J⁻¹) = g 0`
by `anderson_lemma_loss` at `y := −u`, `S := J⁻¹` (`PosSemidef` from `hJ_pd.inv`).
So `g 0 ≤ g u` for all `u`; if `u₀ ≠ 0` then `hunique` at `u := 0` gives `g u₀ < g 0 ≤ g u₀`,
contradiction. Hence `u₀ = 0`.

### `bayes_estimator_asymptotics_bowlShaped`
Rewrite `u₀ = 0` (previous target) into `bayes_estimator_weakConverges`.

## Done

Gate green + `#print axioms bayes_estimator_asymptotics` clean. Report closed/left.
Sanctioned NAMED DEBT (max 1): `bpe_tight` if the three-way split resists — but then
`bayes_estimator_asymptotics` must still be closed from `bpe_tight`'s statement.
