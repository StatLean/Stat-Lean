# bayes4-debt-localtv — close `local_tv_tendsto` (Step B assembly) [debt lane]

Branch `bay/debt-localtv`. The shared rules above apply. **Single target — the last piece of
vdV Theorem 10.1's Step B.**

## Touch-set (ONLY this file)

- `StatLean/Bayesian/BernsteinVonMises/LocalApproximation.lean`

Gate: `lake build StatLean.Bayesian.BernsteinVonMises.LocalApproximation`

## The one target

`local_tv_tendsto`: for every fixed `R > 0` and `δ > 0`,
`P^n_{θ₀} { δ ≤ tvDist ((localPosterior n ω)[|B̄ R]) ((gauss n ω)[|B̄ R]) } → 0`.

**Everything feeding it is already proved in this file** (do not redo):
`measurable_bvmNumer`, `cond_bvmGaussian_apply` (conditioned Gaussian as a
`bvmGaussDens`-ratio), `cond_bvmLocalPosterior_apply_ae` (conditioned local posterior as a
`bvmNumer`-ratio, predictive-a.e., valid once `R < r₀√n`), `bvmLogRatio_tendsto` (for FIXED
`g, h`, the log pair ratio → 0 in `P^n_{θ₀}`-probability), plus the private helpers already
in the file.

Also available (all 0-sorry on your base):
* `MixtureContiguity.lean`: `bvmMixture`, `bvmMixture_absolutelyContinuous`,
  `mutuallyContiguous_mixture_base`, `measure_tendsto_zero_of_predictive_null`;
* `Bayesian/ForMathlib/TVDist.lean`: **`tvDist_normalize_le_double_lintegral`** (the
  pair-ratio Jensen bound — this is the engine), `one_sub_lintegral_le_lintegral_one_sub`
  (now with its measurability hypothesis), `tvDist_le_one`, `measurable_tvDist_kernel`;
* `AsymptoticStatistics/ForMathlib/MultivariateGaussianDensity.lean`: the two-sided
  Gaussian/Lebesgue comparisons (`exists_forall_multivariateGaussian_le_smul_volume`,
  `exists_pos_smul_volume_le_multivariateGaussian`), uniform tails;
* `PriorSmallBall.lean` (0-sorry): `prior_smallBall_upper/lower`.

## Intended route (vdV pp. 142–143, as transcribed in the module docstring)

Fix `R` and `δ`. Let `C := closedBall 0 R`.

1. **Good event.** Work on `Gₙ ⊆ (Fin n → 𝓧)` where simultaneously
   (a) the two a.e. ratio identities hold (their failure set is predictive-null, hence
       `P^n_{θ₀}`-negligible by `measure_tendsto_zero_of_predictive_null`);
   (b) `‖scoreSum sc n ω‖ ≤ K` (score-CLT tightness; if a tightness lemma is not at hand,
       prove a small `private` one from `scoreSum_weakly_converges` + portmanteau on the
       closed ball, or from Chebyshev);
   (c) `bvmNumer M f θ₀ n C ω ≠ 0`.
   Show `P^n_{θ₀}(Gₙᶜ) → 0` (for (c): on the complement the conditioned posterior is junk;
   bound its probability via the same predictive-null/mixture route, or fold (c) into (a)).
2. **Pointwise Jensen bound on `Gₙ`.** Both conditioned measures are normalizations of
   densities against `volume.restrict C`: the posterior side by
   `cond_bvmLocalPosterior_apply_ae` with density `bvmJointDens`, the Gaussian side by
   `cond_bvmGaussian_apply` with density `bvmGaussDens`. Apply
   `tvDist_normalize_le_double_lintegral` with `s := bvmJointDens …`, `t := bvmGaussDens …`
   to get
   `tvDist ≤ ∫⁻ h, (∫⁻ g, (1 − s(g)t(h)/(s(h)t(g))) d(condGauss)) d(condPost)`,
   and note `s(g)t(h)/(s(h)t(g)) = exp (bvmLogRatio … g h ω)` (this identity is pure
   algebra from the two `def`s — prove it as a `private` lemma; mind `ofReal`/`exp`
   positivity so the division is legitimate).
3. **Replace both outer measures by normalized Lebesgue on `C`.** On the event `‖Δₙ‖ ≤ K`,
   `exists_pos_smul_volume_le_multivariateGaussian` and
   `exists_forall_multivariateGaussian_le_smul_volume` give
   `c₁ λ_C ≤ condGauss ≤ c₂ λ_C` with constants depending only on `(R, K, J)`; similarly the
   conditioned posterior is dominated using `prior_smallBall_upper/lower` on the rescaled
   ball. Since the integrand is in `[0,1]`, this converts the double integral into
   `C' * ∫⁻∫⁻ (1 − exp(bvmLogRatio)) dλ_C dλ_C` up to a constant.
4. **Take `P^n_{θ₀}`-expectations and use Fubini + bounded convergence.** The integrand is
   `≤ 1`; for FIXED `(g,h)`, `bvmLogRatio → 0` in probability
   (`bvmLogRatio_tendsto`), so `(1 − exp(bvmLogRatio))⁺ → 0` in probability, and its
   expectation → 0 (bounded convergence for in-probability convergence of `[0,1]` variables:
   `E[X_n] ≤ ε + P(X_n > ε)`). Then integrate over `(g,h) ∈ C × C` with
   `lintegral_lintegral_swap` / dominated convergence (dominator `1`, finite measure
   `λ_C × λ_C`).
5. **Markov** turns the vanishing expectation into the vanishing probability of
   `{δ ≤ tvDist …}`, on `Gₙ`; add `P^n_{θ₀}(Gₙᶜ) → 0`.

Practical advice: commit after each `private` step lemma (the good event, the ratio-identity,
the λ_C comparison, the expectation bound). If the full assembly still resists at the end,
leave `local_tv_tendsto` sorried but KEEP all the private step lemmas closed and report
exactly which step blocked.

## Done

Gate green. Report closed/left plus the tail of `lake build`.
