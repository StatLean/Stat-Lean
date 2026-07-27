# bayes4-conc — prior small-ball bounds + Step A posterior concentration [wave 2]

Branch `bay/bvm-conc`. The shared rules above apply.

## Touch-set (ONLY these files)

- `StatLean/Bayesian/BernsteinVonMises/PriorSmallBall.lean`
- `StatLean/Bayesian/BernsteinVonMises/PosteriorConcentration.lean`

Gate: `lake build StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration`

Newly available on your base branch (closed in wave 1 — trust the statements): the TVDist
and MultivariateGaussianDensity bricks; `Basic.lean` scale-inverse lemmas; the Lemma-10.3
tests (`exponential_tests` etc. — you consume only the `IsExpConsistentTestSeq` hypothesis
shape, not the construction). `MixtureContiguity.lean` (parallel lane) provides the FROZEN
statements `bvmMixture_absolutelyContinuous`, `mutuallyContiguous_mixture_base`,
`measure_tendsto_zero_of_predictive_null` — use them freely (their proofs may land later;
your gate builds them as sorries, which is fine).

Provided 0-sorry upstream (verified on the pin):
- `StatLean.Bayesian.posterior_apply_eq_div` / `posterior_lintegral_eq_div`
  (`Dominated/PosteriorLintegral.lean`) — predictive-a.e. set/lintegral ratio identities;
  `posterior_iid_eq_withDensity_prod_likelihood` (`Updating/IID.lean`);
  `iidKernel_withDensity`, `measurable_uncurry_prod_likelihood` (`ForMathlib/IIDKernel.lean`);
  `ProbabilityTheory.compProd_posterior_eq_map_swap` (Mathlib posterior disintegration).
- Lebesgue volume facts: `EuclideanSpace` has `volume`; ball volumes scale as `r^k`
  (`MeasureTheory.Measure.addHaar_ball` / `addHaar_closedBall` — loogle '"addHaar_ball"';
  the dimension is `finrank ℝ (EuclideanSpace ℝ (Fin k)) = k`).
- Gaussian-type tail integral: `∫_{‖h‖ ≥ M} e^{−c‖h‖²} dh → 0` — derive from
  monotone/dominated convergence with the integrable envelope `e^{−c‖h‖²}`
  (integrability via comparison with the Gaussian density brick or radial computation —
  `MeasureTheory.integrable_exp_neg_mul_sq`-style 1-D + product, or cite
  `ProbabilityTheory.multivariateGaussian`-mass finiteness through the constant-free
  density lemma: `volume.withDensity (exp(−q/2))` is finite since it is `c⁻¹ • N(0,S)`).

## Per-file targets

### PriorSmallBall.lean
- `prior_ball_inv_sqrt_lower`: continuity + positivity at `θ₀` give `f ≥ f θ₀ / 2` on a
  ball `B(θ₀, D₁)`; for `n` with `u/√n ≤ D₁ ≤ r₀`,
  `π(B(θ₀,u/√n)) = ∫_{ball} ofReal f dvol ≥ ofReal (f θ₀/2) · vol(ball(u/√n))`
  (`hπ.restrict_eq` + `withDensity_apply` + `setLIntegral_mono`); ball volume
  `= (u/√n)^k · vol(unit ball)`; package the constant.
- `prior_smallBall_upper` / `prior_smallBall_lower`: same density-envelope argument with
  `f ≤ f θ₀ + f θ₀ = 2 f θ₀`-style two-sided bounds from `ContinuousAt` (choose the ε of
  continuity as `f θ₀ / 2`).
- `prior_tail_split`: split the domain at the `D` of `prior_smallBall_upper`:
  moderate zone `{Mₙ/√n ≤ ‖θ−θ₀‖ < D}`: density bound converts the π-integral to a
  Lebesgue integral; substitute `h := √n(θ−θ₀)` (affine change of variables, Jacobian
  `(√n)^{-k}` cancels the `(√n)^k` prefactor); on this zone `n·min(‖θ−θ₀‖²,1) ≥ ‖h‖²·min(1, …)`
  — carefully: `n‖θ−θ₀‖² = ‖h‖²` and `‖θ−θ₀‖ < D ≤ 1` wlog (shrink `D`), so the exponent
  is `≥ c‖h‖²` when `‖θ−θ₀‖ ≤ 1`... (if `D > 1` shrink `D` to `min D 1`); the resulting
  bound is `C ∫_{‖h‖ ≥ Mₙ} e^{−c‖h‖²} dh → 0`.
  Far zone `{‖θ−θ₀‖ ≥ D}`: `min(‖θ−θ₀‖²,1) ≥ min(D²,1) > 0`, so the integrand is
  `≤ e^{−c·min(D²,1)·n}` and the zone bound is `(√n)^k e^{−c' n} · π(univ) → 0`
  (`Filter.Tendsto` of `polynomial × exp-decay` — `tendsto_pow_mul_exp_neg_atTop`-style,
  loogle '"pow_mul_exp"').

### PosteriorConcentration.lean
- `bvmLocalPosterior_compl_ball`: unfold `bvmLocalPosterior = Kernel.map … (bvmLocalScale)`;
  `Kernel.map_apply'` (measurable set) + `Measure.map_apply`; the preimage of
  `(ball 0 R)ᶜ` under `θ ↦ √n(θ−θ₀)` is `{θ | R/√n ≤ ‖θ−θ₀‖}` — pure norm algebra with
  `Real.sqrt n > 0` (`hn`), `norm_smul`, `Real.sqrt` positivity; mind `ball`(strict) vs the
  `≤` set: `‖√n(θ−θ₀)‖ ≥ R ↔ ‖θ−θ₀‖ ≥ R/√n` (multiply/divide by `√n > 0`).
- `mixture_posterior_test_bound`: `bvmMixture = iidKernel κ n ∘ₘ (π[|Bₙ])`; expand
  `Measure.bind`-lintegral (`MeasureTheory.lintegral_bind` — kernel measurability from
  `iidKernel`); swap to the joint via the disintegration
  `compProd_posterior_eq_map_swap` restricted to the conditioned prior (or direct:
  `∫⁻ ω, Post(ω)(A)·w(ω) d(κₙ ∘ₘ π') ≤ (π Bₙ)⁻¹ ∫⁻ ω, Post(ω)(A)·w(ω) d(κₙ ∘ₘ π)` by the
  smul-domination of the conditioned prior, then the FULL-prior joint identity:
  `∫⁻ ω, Post(ω)(A)·w(ω) d(κₙ ∘ₘ π) = ∫⁻ θ in A, ∫⁻ ω, w ω d(iidKernel κ n θ) dπ` —
  this is Fubini through `compProd_posterior_eq_map_swap` + `Measure.lintegral_compProd`;
  β-reduction gotcha: use `simp_rw` after `compProd` rewrites).
- `posterior_mass_compl_ball_tendsto` (Step A headline): fix `δ`; the deviation event
  splits by the test: `{Post(tailₙ) ≥ δ} ⊆ {φₙ ≥ 1/2-ish} ∪ ({Post(tailₙ)(1−φₙ) ≥ δ/2})`
  — more precisely use Markov twice under `P^n_{θ₀}`:
  `P(Post ≥ δ) ≤ P(φₙ ≥ 1/2) + P(Post·(1−φₙ)-damped event)`; `P^n_{θ₀}(φₙ ≥ 1/2) ≤
  2·∫φₙ dP^n_{θ₀} → 0` (Markov, hφ.typeI); for the damped part, take
  `bvmMixture`-expectations: Markov gives
  `bvmMixture{Post(tailₙ)(1−φₙ) ≥ δ'} ≤ δ'⁻¹ ∫ Post(tailₙ)(1−φₙ) d(bvmMixture)`, bounded
  by `mixture_posterior_test_bound` at `A := tailₙ`; then `hφ.typeII` +
  `prior_ball_inv_sqrt_lower` + `prior_tail_split` make the bound → 0; transfer the
  vanishing `bvmMixture`-probability to `P^n_{θ₀}` by `mutuallyContiguous_mixture_base`.
  Watch the event-measurability requirements of `Contiguous` — posterior masses are
  measurable in `ω` (`Kernel.measurable_coe` of the posterior kernel), tests measurable.

## Done

Gate green. Report per-target closed/left. Sanctioned NAMED DEBT (max 1):
`posterior_mass_compl_ball_tendsto` (only if the final assembly resists — everything
feeding it must close).
