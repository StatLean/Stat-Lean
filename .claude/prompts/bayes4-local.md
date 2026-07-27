# bayes4-local — Step B: mixture contiguity + local Gaussian approximation [wave 2]

Branch `bay/bvm-local`. The shared rules above apply. This is the mathematical heart of the
Bernstein–von Mises proof — budget your time-boxes; the single sanctioned headline debt is
`local_tv_tendsto` (isolate it if the final assembly resists, but close everything feeding
it).

## Touch-set (ONLY these files)

- `StatLean/Bayesian/BernsteinVonMises/MixtureContiguity.lean`
- `StatLean/Bayesian/BernsteinVonMises/LocalApproximation.lean`

Gate: `lake build StatLean.Bayesian.BernsteinVonMises.LocalApproximation`

Newly available on your base branch (closed in wave 1 — trust the statements):
- `StatLean/Bayesian/ForMathlib/TVDist.lean` (tvDist triangle/map/cond/withDensity,
  `one_sub_lintegral_le_lintegral_one_sub`, `lintegral_le_lintegral_add_tvDist`,
  `tvDist_normalize_le_double_lintegral`, `measurable_tvDist_kernel`);
- `StatLean/AsymptoticStatistics/ForMathlib/MultivariateGaussianDensity.lean`
  (constant-free density, tilt, two-sided λ-comparisons, uniform tails);
- `StatLean/AsymptoticStatistics/ForMathlib/ContiguityIntegralComparison.lean`
  (`mutuallyContiguous_of_log_normal_of_integral_comparison`, `Contiguous.comp_subseq`);
- `StatLean/Bayesian/BernsteinVonMises/Basic.lean` (scale-inverse lemmas).

Provided 0-sorry upstream (verified on the pin):
- `AsymptoticRepresentation.productMeasure_integral_comparison_boundedMeasurable`
  (`LocalAsymptoticNormality/AsymptoticRepresentation.lean:1713`) — the ρₙ comparison for
  bounded measurable `g`; instance argument `[∀ θ n, IsProbabilityMeasure (productMeasure …)]`
  is discharged via `haveI := fun θ n => productMeasure_isProbabilityMeasure M μ hPDF θ n`.
- `AsymptoticRepresentation.lanResidual_tendsto_productMeasure` (same file, ~line 880) —
  the per-`h` LAN residual under `P^n_{θ₀}` in `.real` unrolled form; hypothesis bundle
  `(h_one, hint, h_one_perturb, hint_perturb)` all follow from `hPDF`
  (`hPDF.density_integral_eq_one`, `hPDF.density_integrable`).
- `AsymptoticRepresentation.scoreSum_weakly_converges` (score CLT, needs `hJ_psd :=
  hJ_pd.posSemidef`); `AsymptoticStatistics.multivariateGaussian_map_inner_eq_gaussianReal`
  and `integral_exp_inner_multivariateGaussian` (`ForMathlib/GaussianMGF.lean`);
  `AsymptoticStatistics.WeakConverges.map` / `.slutsky_of_tendstoInMeasure_dist`
  (`ForMathlib/Contiguity.lean`, `ForMathlib/Slutsky.lean`).
- Posterior identities (predictive-a.e.):
  `StatLean.Bayesian.posterior_iid_eq_withDensity_prod_likelihood` (`Updating/IID.lean`),
  `posterior_apply_eq_div`, `posterior_lintegral_eq_div` (`Dominated/PosteriorLintegral.lean`),
  `iidKernel_withDensity` (`ForMathlib/IIDKernel.lean`).
- `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`
  (`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:277`);
  `Filter.tendsto_of_subseq_tendsto`.
- DQM singular-mass controls: `AsymptoticStatistics.dqm_perturbation_deficit_mass_tendsto` /
  `dqm_perturbation_excess_mass_tendsto` (`DQM/Properties.lean:729/864`).

## Per-file targets

### MixtureContiguity.lean
- `bvmMixture_absolutelyContinuous`: `cond = (π B)⁻¹ • π.restrict B`; `Measure.bind` is
  monotone in the input measure; `restrict ≤ π` gives
  `bvmMixture ≤ (π B)⁻¹ • (iidKernel κ n ∘ₘ π)`; smul-domination ⇒ `≪`
  (`Measure.absolutelyContinuous_of_le_smul` — find exact name via loogle
  '"absolutelyContinuous" "smul"').
- `logLikelihood_weakConverges`: decompose
  `Lₙ = ⟪h, scoreSumₙ⟫ − ½⟪h,Jh⟫ + residₙ`; `⟪h, ·⟫` pushforward of the score CLT gives
  `gaussianReal 0 ⟪h,Jh⟫` (`multivariateGaussian_map_inner_eq_gaussianReal` — check its
  exact statement/orientation); shift by the constant `−½⟪h,Jh⟫` (`WeakConverges.map` with
  the continuous `· + c`, or a dedicated shift lemma); kill `residₙ` by Slutsky
  (`slutsky_of_tendstoInMeasure_dist` with `lanResidual_tendsto_productMeasure` converted
  from `.real`-form to `TendstoInMeasure` — `ENNReal.tendsto_toReal_zero_iff`-style, see
  `AsymptoticRepresentation.lean:1017` for the conversion idiom).
- `mutuallyContiguous_local_alternative`: feed
  `mutuallyContiguous_of_log_normal_of_integral_comparison` with `L := logLikelihood`,
  the comparison from `productMeasure_integral_comparison_boundedMeasurable`, and
  `logLikelihood_weakConverges` (package `v := ⟨⟪h,Jh⟫, nonneg⟩`; nonnegativity of the
  quadratic form from `hJ_pd.posSemidef` + `hJ` + `fisherInformation` being an integral of
  squares, or directly `Matrix.PosDef` ⟹ `0 ≤ ⟪h, Jh⟫`).
- `mutuallyContiguous_mixture_base`: both directions via the prior two-sided volume
  comparison on the shrinking ball. NOTE: `prior_smallBall_upper/lower` live in
  `PriorSmallBall.lean` (another lane) — do NOT import it (it is outside your touch-set's
  import cone? It IS imported by MixtureContiguity — you may USE its frozen statements;
  they may still be sorried, that is fine). Direction `mixture ⊲ base`: for events `Aₙ` with
  `P_{n,0}(Aₙ) → 0`, write `bvmMixture(Aₙ) = (π Bₙ)⁻¹ ∫_{Bₙ} P^n_θ(Aₙ) dπ(θ)`
  (`Measure.bind_apply` + cond); substitute `θ = θ₀ + h/√n`, compare `π|_{Bₙ}` with
  Lebesgue two-sidedly, reduce to `(vol U)⁻¹ ∫_U P_{n,h}(Aₙ) dh → 0`; pointwise-in-`h`
  convergence by `mutuallyContiguous_local_alternative` (constant `h`), dominated by 1 ⇒
  DCT. Direction `base ⊲ mixture`: subsequence extraction
  (`TendstoInMeasure.exists_seq_tendsto_ae` on the `L¹(dh)` convergence), pick a single
  good `h`, apply per-`h` contiguity along the subsequence (`Contiguous.comp_subseq`),
  conclude by `Filter.tendsto_of_subseq_tendsto`.
- `measure_tendsto_zero_of_predictive_null`: `hN n` ⇒ `bvmMixture(N n) = 0` exactly
  (`bvmMixture_absolutelyContinuous`); constants tend to 0; transfer by
  `mutuallyContiguous_mixture_base` (direction mixture → base).

### LocalApproximation.lean
- `measurable_bvmNumer`: `Measurable.lintegral_prod_right'`-style (the integrand is jointly
  measurable in `(h, ω)`: products of compositions of `hM_joint` with measurable maps,
  times the `f`-factor); use `Measurable.lintegral_prod_right` on `volume.restrict C`.
- `cond_bvmGaussian_apply`: `bvmGaussian = N(Δₙ, J⁻¹)`; by
  `multivariateGaussian_eq_smul_withDensity` + `multivariateGaussian_eq_withDensity_tilt`,
  `N(Δₙ,J⁻¹) = c(ω) • volume.withDensity (bvmGaussDens · ω)` with
  `c(ω) ∈ (0,∞)` (identify `⟪JΔₙ, h⟫ = ⟪scoreSumₙ, h⟫` from `J·toEuclideanCLM J⁻¹ = id`
  on PosDef); `cond` of a positive-scalar multiple: the scalar cancels
  (`ProbabilityTheory.cond_smul`-type — if absent, unfold `cond` and compute with
  `Measure.smul_apply`); then `cond_apply` + `withDensity_apply`.
- `cond_bvmLocalPosterior_apply_ae`: start from
  `posterior_iid_eq_withDensity_prod_likelihood` (a.e. predictive); push through
  `Kernel.map … (bvmLocalScale)` (`Kernel.map_apply'` + `Measure.map_apply`); change
  variables `θ = bvmLocalUnscale h` in the π-integrals using
  `hπ.restrict_eq` (the prior is `volume.withDensity f` on the ball; the rescaled ball
  `C/√n + θ₀ ⊆ B(θ₀,r₀)` by `hn`), `MeasurePreserving`-style Lebesgue scaling: volume of
  the affine image contributes the constant Jacobian `(√n)^{-k}` to BOTH numerator and
  denominator-restricted-to-C — it cancels in the ratio (mind: the posterior normalizer in
  the a.e. identity integrates over ALL of Θ, but after conditioning on `C` the normalizer
  becomes the C-restricted mass — derive the conditional from the set-form
  `posterior_apply_eq_div` applied to `A ∩ scaled-C` and `scaled-C`, then divide).
  For the Lebesgue affine change of variables use
  `MeasureTheory.Measure.map_addHaar_smul` / translation invariance (loogle
  '"addHaar" "smul"') or `volume`-specific lemmas on `EuclideanSpace`
  (`EuclideanSpace.volume_preserving…`; the map is `h ↦ θ₀ + (√n)⁻¹ • h`).
- `bvmLogRatio_tendsto`: `bvmLogRatio = residₙ(g) − residₙ(h) + priorLogRatioₙ` where
  `residₙ(x) := Lₙ(x) − (⟪x, scoreSumₙ⟫ − ½⟪x,Jx⟫)` — check the algebra against the defs
  (expand; the `⟪g−h, scoreSum⟫` and quadratic terms recombine exactly);
  `lanResidual_tendsto_productMeasure` at `g` and at `h` (two calls); the prior term is
  deterministic: `f` continuous and positive at `θ₀` ⇒
  `log f(θ₀ + g/√n) − log f(θ₀ + h/√n) → 0` (`ContinuousAt.tendsto`, `Real.log`
  continuity at the positive value `f θ₀`; `bvmLocalUnscale θ₀ n x → θ₀` as `n → ∞` since
  `(√n)⁻¹ → 0`); combine with the triangle inequality on the deviation events.
- `local_tv_tendsto` (HEADLINE): assemble per the module docstring. Skeleton:
  (i) fix `δ`; work on the good event `Gₙ` where (a) the a.e. ratio identities hold
  (complement predictive-null → use `measure_tendsto_zero_of_predictive_null`),
  (b) `‖scoreSumₙ‖ ≤ K` (score-CLT tightness — prove inline via
  `scoreSum_weakly_converges` + portmanteau closed-ball bound, or crude Chebyshev on
  `‖scoreSum‖²` if simpler), (c) `bvmNumer C > 0` (on the event, the denominator dominates
  a positive quantity — the prior lower comparison + exp positivity; if delicate, fold the
  `bvmNumer C = 0` event into (a)–(b) style negligibility).
  (ii) On `Gₙ`, both conditioned measures are normalized densities over
  `volume.restrict C`: apply `tvDist_normalize_le_double_lintegral` with
  `s := bvmJointDens`, `t := bvmGaussDens` — the pair ratio is `exp(bvmLogRatio)` up to
  the exact algebra.
  (iii) Bound the double integral: replace the two outer integrators by multiples of
  normalized Lebesgue on `C` (Gaussian side: two-sided comparison bricks with means
  bounded by `K`; posterior side: it is the measure you integrate against — vdV's trick:
  after the Jensen bound the outer measure is the conditioned posterior itself; take
  `P_{n,C}`-expectations and use Fubini to land in the mixture-tilted triple measure —
  follow vdV p. 143 as transcribed in the module docstring).
  (iv) The triple-integral integrand `(1 − exp(bvmLogRatio))⁺ ≤ 1` and → 0 in probability
  per fixed `(g,h)` (`bvmLogRatio_tendsto` + continuity of `x ↦ (1 − e^x)⁺` at 0); lift by
  DCT over `λ_C × λ_C` and take expectations (bounded convergence).
  (v) Transfer the resulting `P_{n,C}`-mean convergence to `P^n_{θ₀}`-probability via
  Markov + `mutuallyContiguous_mixture_base`.
  If (iii)–(iv) resist as one block, prove and commit intermediate `private` lemmas for
  each displayed inequality; the named debt (if any) must be exactly `local_tv_tendsto`.

## Done

Gate green. Report per-target closed/left + the exact statement of any obstruction.
Sanctioned NAMED DEBT (max 1): `local_tv_tendsto`.
