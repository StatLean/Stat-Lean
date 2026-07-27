# bayes4-bricks — Gaussian density, TV, and contiguity bricks [wave 1]

Branch `bay/bvm-bricks`. The shared rules above apply.

## Touch-set (ONLY these files)

- `StatLean/AsymptoticStatistics/ForMathlib/MultivariateGaussianDensity.lean`
- `StatLean/AsymptoticStatistics/ForMathlib/ContiguityIntegralComparison.lean`
- `StatLean/Bayesian/ForMathlib/TVDist.lean`
- `StatLean/Bayesian/ForMathlib/GaussianTV.lean`
- `StatLean/Bayesian/BernsteinVonMises/Basic.lean`

Gate: `lake build StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity StatLean.AsymptoticStatistics.ForMathlib.ContiguityIntegralComparison StatLean.Bayesian.ForMathlib.TVDist StatLean.Bayesian.ForMathlib.GaussianTV StatLean.Bayesian.BernsteinVonMises.Basic`

Provided 0-sorry (verified on the pin — reuse, do not reprove):
- `ProbabilityTheory.multivariateGaussian` (def: pushforward of `stdGaussian` by
  `μ + toEuclideanCLM (CFC.sqrt S) x`; `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`),
  `stdGaussian_eq_map_pi_orthonormalBasis`, `map_pi_eq_stdGaussian`, `charFun_multivariateGaussian`,
  `Measure.ext_of_charFun` (`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`).
- StatLean `AsymptoticStatistics.multivariateGaussian_map_toEuclideanCLM`
  (`(N(μ,S)).map (toEuclideanCLM A) = N(Aμ, A*S*Aᴴ)`, needs `S.PosSemidef`) and
  `multivariateGaussian_withDensity_exp_shift` — both in `ForMathlib/GaussianMGF.lean`;
  CFC.sqrt manipulation patterns at `GaussianMGF.lean:563-583`.
- StatLean `pi_gaussianReal_eq_withDensity` (`ForMathlib/PiGaussian.lean`),
  `stdGaussian_absolutelyContinuous_volume`, `multivariateGaussian_absolutelyContinuous_volume_of_posDef`
  (`ForMathlib/MultivariateGaussianWeakLimit.lean`).
- Mathlib `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`
  (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`) for the `|det|` factor.
- StatLean `StatLean.Minimaxity.tvDist`, `tvDist_comm`, `tvDist_le_one`,
  `tvDist_eq_half_lintegral`, `one_sub_tvDist_eq_iInf` (`Minimaxity/ForMathlib/TotalVariation.lean`);
  `StatLean.Minimaxity.pinsker_tv_le_kl : tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1/2 : ℝ)`;
  `klDiv_multivariateGaussian_smul_one` + whitening helpers (`klDiv_map_eq_of_comp`,
  `map_multivariateGaussian_clm`) in `Minimaxity/ForMathlib/GaussianKLMulti.lean`.
- StatLean Contiguity toolbox (`AsymptoticStatistics/ForMathlib/Contiguity.lean`):
  `Contiguous` def (event sequences), `contiguous_of_asymptotically_log_normal`,
  `uniform_integrability_exp_L`, `uniform_integrability_exp_L_of_integral_tendsto_one`,
  `WeakConverges` + portmanteau via Mathlib (`MeasureTheory.limsup_measure_closed_le_of_tendsto`-family).
- Mathlib `ProbabilityTheory.Kernel.rnDeriv` + `Kernel.measurable_rnDeriv`
  (`Mathlib/Probability/Kernel/RadonNikodym.lean`, needs `[CountablyGenerated]` target),
  `Kernel.rnDeriv_eq_rnDeriv_measure`.

## Per-file targets

### MultivariateGaussianDensity.lean
- `multivariateGaussian_map_const_add`: unfold the def, `Measure.map_map` (mind the
  direction, CLAUDE gotcha: forward collapses), `zero_add` congruence.
- `multivariateGaussian_map_matrix_inv`: apply `multivariateGaussian_map_toEuclideanCLM`
  with `A := J⁻¹`, `S := J`; close `J⁻¹ * J * (J⁻¹)ᴴ = J⁻¹` via `hJ.posSemidef`,
  `Matrix.PosDef.isHermitian`, `Matrix.PosDef.isUnit_det`/`Matrix.mul_nonsing_inv`.
- `multivariateGaussian_eq_smul_withDensity`: route `stdGaussian = (pi gaussianReal).map b`
  + `pi_gaussianReal_eq_withDensity` + push through `A := toEuclideanCLM (CFC.sqrt S)`
  with `map_linearMap_addHaar_eq_smul_addHaar`; identify the quadratic form via
  `A` self-adjoint and `A ∘ A = toEuclideanCLM S` (GaussianMGF patterns); the constant `c`
  absorbs `(2π)^{-d/2}` and `|det A|⁻¹` — do NOT compute it.
- `multivariateGaussian_eq_withDensity_tilt`: `multivariateGaussian_withDensity_exp_shift`
  at `h := toEuclideanCLM S⁻¹ m`; close `toEuclideanCLM S (toEuclideanCLM S⁻¹ m) = m` and
  match the quadratic-form scalars.
- `exists_forall_multivariateGaussian_le_smul_volume`: from the density lemma; the density
  `exp(−q(x)/2) ≤ 1`; translation invariance of `volume` handles the mean; extend to
  arbitrary sets via `measure_mono` + outer-measure hull (`exists_measurable_superset`).
- `exists_pos_smul_volume_le_multivariateGaussian`: density lower bound
  `exp(−q(x−m)/2) ≥ exp(−sup_{‖y‖ ≤ R+r} q(y)/2)` on the ball; continuity of `q` on a
  compact ball gives the finite sup.
- `multivariateGaussian_compl_closedBall_uniform_small`: `N(m,S)((B̄ M)ᶜ) ≤ N(0,S)((B̄ (M−R))ᶜ)`
  by translation; then `tendsto_measure_iInter`-type monotone continuity of `N(0,S)` on
  shrinking complements (`MeasureTheory.tendsto_measure_biInter_gt` or direct: the
  complements have empty intersection, finite measure). Degenerate `S` (non-PosSemidef):
  `multivariateGaussian_of_not_posSemidef` = Dirac — handle by cases.
- `gaussian_loss_convolution_lt_top`: bound `ℓ(u−z) ≤ 1 + ‖u−z‖^p ≤` polynomial in `‖z‖`;
  Gaussian moments finite (via the density lemma + `Real.Gamma`-free route: compare with
  `exp(−q/4)` integrability, or use `IsGaussian.memLp_dual`-style moment facts; a crude
  `∫ (1+‖z‖)^p e^{−c‖z‖²} dz < ∞` argument suffices).
- `gaussian_loss_convolution_continuous`: write the integral against
  `c · volume.withDensity(exp(−q/2))` (density lemma), substitute `y := u − z` (volume
  translation invariance) to move `u` into the smooth density, then dominated convergence
  (`MeasureTheory.tendsto_lintegral_of_dominated_convergence`) with a locally uniform
  dominating envelope. This is the hardest target of the file — time-box accordingly; it is
  a sanctioned NAMED DEBT if it resists (leave the sorry, close the rest).

### ContiguityIntegralComparison.lean
- `Contiguous.comp_subseq`: given events `A n` on `Ω (φ n)`, define padded events on the
  full sequence by `B m := if h : ∃ n, φ n = m then (cast) A (choice) else ∅` — simpler:
  directly verify the definition using `Filter.tendsto_of_subseq...`? No: apply `hPQ` to the
  padded family `B` with `B (φ n) = A n`, `B m = ∅` otherwise (use `Nat.find`-free
  construction: `B m := ⋃ n ∈ {n | φ n = m}, A n`-style with the cast via `hφ.injective`;
  `measure ∅ = 0` handles off-subsequence indices; `Tendsto (P ∘ φ) atTop 0` extends to the
  padded sequence since off-indices give `0`). Extract the subsequence limit back with
  `hφ.tendsto_atTop`.
- `mutuallyContiguous_of_log_normal_of_integral_comparison`: BOTH directions.
  `Q ⊲ P`: for events `Aₙ`, `g n := indicator (A n)` (bounded by 1) in the comparison gives
  `|Qₙ(Aₙ) − ∫_{Aₙ} exp(Lₙ) dPₙ| ≤ ρₙ`; the comparison at `g ≡ 1` gives
  `∫ exp(Lₙ) dPₙ → 1`; then `uniform_integrability_exp_L_of_integral_tendsto_one` + the
  truncation argument inside `contiguous_of_asymptotically_log_normal` (mimic its proof —
  read it; the exact-identity step is replaced by the ρₙ error term).
  `P ⊲ Q`: split `Pₙ(Aₙ) ≤ Pₙ(Aₙ ∩ {Lₙ ≥ −M}) + Pₙ(Lₙ < −M)`; on the first set
  `1 ≤ e^M e^{Lₙ}` so `Pₙ(Aₙ ∩ {Lₙ ≥ −M}) ≤ e^M ∫_{Aₙ} e^{Lₙ} dPₙ ≤ e^M (Qₙ(Aₙ) + ρₙ)`;
  `limsup Pₙ(Lₙ < −M) ≤ N(−v/2,v)((−∞,−M])` by portmanteau (closed set), which is `< ε` for
  `M` large. Assemble with an ε/3 argument.

### TVDist.lean
- `tvDist_triangle`, `tvDist_map_le`, `tvDist_map_measurableEmbedding`: from the sup-form
  def (`tvDist = ⨆ s meas, μ s − ν s` truncated); embedding case: preimages of measurable
  sets biject with measurable subsets of the range (`MeasurableEmbedding.measurableSet_image`).
- `tvDist_cond_le`: `ProbabilityTheory.cond` is `(μ C)⁻¹ • μ.restrict C`; two one-sided
  estimates as in the docstring; `ENNReal.div` algebra.
- `tvDist_withDensity_eq`: via `tvDist_eq_half_lintegral` with `ξ := μ + ν` replaced by the
  common base: use `withDensity_add_left`-style rewrites, or prove directly from the sup
  form: `μ s − ν s = ∫_s (p − q) ≤ ∫ (p − q)⁺` with equality at `s = {p > q}` (measurable).
- `one_sub_lintegral_le_lintegral_one_sub`: `lintegral_const` + `tsub_le_iff` +
  `lintegral_add`-splitting on `{Y ≤ 1}`; or: `1 = ∫ 1 ≤ ∫ ((1 − Y) + Y) = ∫(1−Y) + ∫Y`
  (`tsub_add_cancel_of_le` pointwise fails for `Y > 1` — but then `1 − Y = 0` and the
  inequality is monotone; case-split pointwise: `1 ≤ (1 − Y x) + Y x` always in ℝ≥0∞).
- `lintegral_le_lintegral_add_tvDist`: layer-cake `lintegral =` `∫₀^∞ μ{w > s} ds`
  (`MeasureTheory.lintegral_eq_lintegral_meas_lt` / `lintegral_eq_lintegral_meas_le` — find
  the pin's name with loogle '"meas_lt"'); `μ{w>s} ≤ ν{w>s} + tvDist` for `s < B`, `= 0`
  contribution above `B`.
- `tvDist_normalize_le_double_lintegral`: the docstring route; work with the a.e.-positivity
  hypotheses to make the ratio manipulations a.e.-valid; Jensen step is
  `one_sub_lintegral_le_lintegral_one_sub`. HARD — sanctioned NAMED DEBT if it resists
  after two attempts.
- `measurable_tvDist_kernel`: `tvDist (κ a) (η a) = ∫⁻ x, (rnDeriv-diff)⁺ d((κ+η) a)`-form
  via `tvDist_eq_half_lintegral` (or the pos-part form you prove for `tvDist_withDensity_eq`);
  joint measurability from `Kernel.measurable_rnDeriv` + `Kernel.lintegral`-measurability
  (`Kernel.measurable_lintegral`).

### GaussianTV.lean
- `klDiv_multivariateGaussian_same_cov`: whiten by `W := toEuclideanCLM (CFC.sqrt S⁻¹)`
  (a measurable equiv for PosDef S — its inverse is `toEuclideanCLM (CFC.sqrt S)`); KL is
  preserved under bijective pushforward (`klDiv_map_eq_of_comp` — read its exact interface);
  reduce to `klDiv (N(W a, 1)) (N(W b, 1))` = `klDiv_multivariateGaussian_smul_one` at
  `c = 1`; identify `‖W(a−b)‖² = ⟪a−b, S⁻¹(a−b)⟫`.
- `tvDist_multivariateGaussian_le`: `pinsker_tv_le_kl` + the KL identity + `ENNReal.rpow`
  algebra (`ENNReal.ofReal_rpow_of_pos`, `2⁻¹ * ofReal x = ofReal (x/2)`).

### Basic.lean (BernsteinVonMises)
- `bvmLocalUnscale_bvmLocalScale` / `bvmLocalScale_bvmLocalUnscale`: `smul_smul`,
  `inv_mul_cancel₀` (`Real.sqrt_ne_zero'`: `√n ≠ 0 ↔ 0 < n`), `add_sub_cancel` /
  `sub_add_cancel` — pure algebra, `simp [bvmLocalScale, bvmLocalUnscale, smul_smul]` +
  `field_simp` should close.
- `measurable_bvmEffScore`: `(toEuclideanCLM J⁻¹).continuous.measurable.comp` of scoreSum
  measurability — find/prove scoreSum measurable: it is `(√n)⁻¹ • ∑ i, sc (ω i)`;
  `Finset.measurable_sum` + `measurable_pi_apply` + `Measurable.const_smul`.

## Done

Gate green; per-target closed/left report. Sanctioned named debts (max 2):
`gaussian_loss_convolution_continuous`, `tvDist_normalize_le_double_lintegral`.
