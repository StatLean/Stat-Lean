# bayes4-assembly — Theorem 10.1 (Bernstein–von Mises) + efficient centering [wave 3]

Branch `bay/bvm-assembly`. The shared rules above apply.

## Touch-set (ONLY these files)

- `StatLean/Bayesian/BernsteinVonMises/Theorem10_1.lean`
- `StatLean/Bayesian/BernsteinVonMises/EfficientCentering.lean`

Gate: `lake build StatLean.Bayesian.BernsteinVonMises.EfficientCentering`
(this pulls in Theorem10_1 and everything below it).

Available on your base branch (closed in waves 1–2 — trust the statements, do NOT reprove):
- **Step A**: `posterior_mass_compl_ball_tendsto` (`PosteriorConcentration.lean`) — for every
  `Mₙ → ∞` and `δ > 0`, `P^n_{θ₀}{ δ ≤ Post(‖θ−θ₀‖ ≥ Mₙ/√n) } → 0`, given
  `IsExpConsistentTestSeq` tests; plus `bvmLocalPosterior_compl_ball` (pushforward
  bookkeeping: local-posterior mass outside `ball 0 R` = θ-posterior mass outside
  `R/√n`).
- **Step B**: `local_tv_tendsto` (`LocalApproximation.lean`) — for every FIXED `R > 0` and
  `δ > 0`, `P^n_{θ₀}{ δ ≤ tvDist (localPosterior[|B̄ R]) (gauss[|B̄ R]) } → 0`.
- **Lemma 10.3**: `exponential_tests` (`ExponentialTests.lean`) — supplies
  `∃ φ c, 0 < c ∧ IsExpConsistentTestSeq M μ θ₀ Mseq c φ` from the DQM/Fisher/tests
  hypotheses. Use it to discharge Step A's test hypothesis.
- **TV toolbox** (`Bayesian/ForMathlib/TVDist.lean`): `tvDist_triangle`, `tvDist_cond_le`
  (`tvDist μ (μ[|C]) ≤ μ Cᶜ / μ C`), `tvDist_map_measurableEmbedding`, `tvDist_map_le`,
  `measurable_tvDist_kernel`.
- **Gaussian bricks** (`AsymptoticStatistics/ForMathlib/MultivariateGaussianDensity.lean`):
  `multivariateGaussian_compl_closedBall_uniform_small` (mean-uniform tail),
  `multivariateGaussian_map_const_add`, `multivariateGaussian_map_matrix_inv`,
  `multivariateGaussian_eq_smul_withDensity`.
- **Gaussian TV** (`Bayesian/ForMathlib/GaussianTV.lean`): `tvDist_multivariateGaussian_le`
  (`tvDist (N(a,S)) (N(b,S)) ≤ (⟪a−b, S⁻¹(a−b)⟫/4)^(1/2)`), `klDiv_multivariateGaussian_same_cov`.
- Score-sum tightness: prove/reuse `scoreSum_uniformly_tight` (stub in `Theorem10_1.lean` —
  it is YOURS to close): from `AsymptoticRepresentation.scoreSum_weakly_converges`
  (score CLT, `hJ_psd := hJ_pd.posSemidef`) + Prokhorov/portmanteau
  (`AsymptoticStatistics.Prohorov.*`, or directly: weak convergence ⇒ tightness of the
  sequence, `MeasureTheory.IsTightMeasureSet`), or crude route: Chebyshev on
  `∫‖scoreSum‖²` (uniformly bounded by `tr J + o(1)` — heavier; prefer portmanteau on the
  closed ball complement with a continuity radius).

## Targets

### Theorem10_1.lean
1. `scoreSum_uniformly_tight` — see above.
2. `bernstein_von_mises` — the triangle argument. Fix `δ > 0`. For each fixed `R`:
   `bvmTV ≤ tvDist(Post, Post[|C_R]) + tvDist(Post[|C_R], N[|C_R]) + tvDist(N[|C_R], N)`
   with `C_R := closedBall 0 R` (`tvDist_triangle` twice).
   - Term 1 `≤ Post(C_Rᶜ)/Post(C_R)` (`tvDist_cond_le`): choose `R := Mₙ` along a sequence
     `Mₙ → ∞` — CAREFUL: Step B needs FIXED `R`, Step A needs `Mₙ → ∞`. Standard
     resolution: prove the `limsup`-in-`R` statement. Concretely: show
     `∀ δ ε > 0, ∃ R, limsup_n P^n_{θ₀}{ δ ≤ bvmTV } ≤ ε`, then conclude the limit is 0
     (`limsup ≤ ε ∀ε ⇒ tendsto 0`, `tendsto_of_le_of_forall_eventually`-style / use
     `ENNReal.le_of_forall_pos_le_add` on the limsup, or `Filter.limsup_le_iff`).
     For the fixed `R`: Term 1 is controlled by Step A applied with the CONSTANT sequence
     `Mseq := fun _ => R`? — NO: Step A's tests need `Mₙ → ∞`. Instead apply Step A with a
     genuine `Mₙ → ∞` (e.g. `Mₙ := √(log (n+2))` or `Mseq n := (n:ℝ)^(1/4)`) to get
     `Post(‖h‖ ≥ Mₙ) →ᵖ 0`, and note `Mₙ ≥ R` eventually, so `Post(C_Rᶜ) ≤ Post(‖h‖ ≥ Mₙ)`
     is NOT the right direction — it is the reverse. Correct: `Post(C_Rᶜ) ≥ Post(‖h‖ ≥ Mₙ)`
     eventually. So Term 1 at fixed `R` does NOT vanish; it is `O(mass outside R)`, which is
     small only for LARGE `R`. That is exactly why the limsup-in-`R` form is needed:
     bound Term 1 by `Post(C_Rᶜ)` whose limsup-in-probability is controlled by the Gaussian
     mass outside `C_R` PLUS the Step-B accuracy at radius `R`… Cleanest route (follow it):
     * (a) By Step A with `Mₙ → ∞`: the localized posterior concentrates.
     * (b) By Step B at radius `R` and the Gaussian tail brick:
       `Post(C_Rᶜ) ≤ N(C_Rᶜ) + 2·tvDist(Post[|C_{R'}], N[|C_{R'}]) + Post(C_{R'}ᶜ)`-type
       chains get circular. AVOID. Use instead the vdV structure literally:
       vdV bounds `‖Post − Post^{C_n}‖ ≤ 2 Post(C_nᶜ)` with `C_n` the ball of radius `Mₙ`
       (Step A gives this → 0 in probability), and Step B for the FIXED-radius balls, then
       says "true for every ball C of fixed radius M, hence also for some `Mₙ → ∞`".
       **Formalize that last sentence as a diagonal extraction**: for each `m : ℕ` apply
       Step B at `R := m` to get `N_m` with
       `∀ n ≥ N_m, P^n_{θ₀}{ 1/m ≤ tvDist(Post[|C_m], N[|C_m]) } ≤ 1/m`; define
       `Mseq n := (the largest m ≤ n with N_m ≤ n)` (monotone, → ∞ since each `N_m` is
       finite); then the mixed statement holds along `Mseq`. Implement `Mseq` with
       `Nat.findGreatest`; prove `Tendsto Mseq atTop atTop` (for every `m`, eventually
       `Mseq n ≥ m`).
     * (c) With this `Mseq`: Term 1 ≤ `2 · Post(C_{Mseq n}ᶜ)` →ᵖ 0 by Step A;
       Term 2 →ᵖ 0 by construction of `Mseq`; Term 3 ≤ `N(C_{Mseq n}ᶜ)/N(C_{Mseq n})`
       →ᵖ 0 by the mean-uniform Gaussian tail brick on the tightness event
       `{‖scoreSum‖ ≤ K}` (`scoreSum_uniformly_tight`) — note `bvmEffScore` is a fixed
       linear image of `scoreSum`, so its norm is `≤ ‖J⁻¹‖ K`.
     * (d) Combine with a union bound over the three `δ/3` events.
3. `bernstein_von_mises_lintegral` — from 2 by bounded convergence:
   `∫ bvmTV ≤ δ + 1·P{bvmTV > δ}` (`tvDist ≤ 1`, `tvDist_le_one`), then `δ ↓ 0`
   (`ENNReal.le_of_forall_pos_le_add` / `tendsto_of_forall...`). Measurability of
   `ω ↦ bvmTV …` from `measurable_tvDist_kernel` (both arguments are kernels:
   `bvmLocalPosterior` is a kernel; the Gaussian side needs a kernel packaging —
   if `bvmGaussian` is not literally a kernel, build the `private` kernel
   `⟨fun ω => bvmGaussian J sc n ω, meas⟩` with measurability from
   `multivariateGaussian`-Feller (`AsymptoticStatistics.multivariateGaussian_kernel_Feller`
   in `ForMathlib/MultivariateGaussianWeakLimit.lean`) composed with
   `measurable_bvmEffScore`).

### EfficientCentering.lean
`bernstein_von_mises_efficient_centering`: chain
   `tvDist(Post_θ, N(θ̂ₙ, n⁻¹J⁻¹))`
   `= tvDist(localPost, N(√n(θ̂ₙ−θ₀), J⁻¹))` — by `tvDist_map_measurableEmbedding` along
   the affine equivalence `bvmLocalScale θ₀ n` (a `MeasurableEmbedding`: it is an affine
   homeomorphism for `n ≥ 1`; build via `Homeomorph`/`MeasurableEquiv` from
   `bvmLocalScale_bvmLocalUnscale` + `bvmLocalUnscale_bvmLocalScale` in `Basic.lean`, then
   `MeasurableEquiv.measurableEmbedding`); the Gaussian side transforms by
   `multivariateGaussian_map_const_add` + `multivariateGaussian_map_matrix_inv`-style
   scaling (`N(m, n⁻¹J⁻¹)` pulled back is `N(√n(m−θ₀), J⁻¹)`; the scalar-matrix pushforward
   `x ↦ √n • x` maps `N(a,S)` to `N(√n a, n S)` — if a scalar-smul Gaussian lemma is
   missing, derive from `multivariateGaussian_map_toEuclideanCLM` at `A := (√n)•1`).
   `≤ tvDist(localPost, N(Δₙ, J⁻¹)) + tvDist(N(Δₙ,J⁻¹), N(√n(θ̂ₙ−θ₀), J⁻¹))`
   — first term →ᵖ 0 by `bernstein_von_mises`; second `≤ (‖J⁻¹‖-weighted ‖Δₙ − √n(θ̂ₙ−θ₀)‖)^{1/2}`
   by `tvDist_multivariateGaussian_le`, →ᵖ 0 by `hest_eff` (continuity of
   `x ↦ (c‖x‖²)^{1/2}` at 0; work with the ε-δ unrolled form: for `δ > 0` pick `ε` with
   the bound `< δ/2`).

## Done

Gate green. Report per-target closed/left. Sanctioned NAMED DEBT (max 1):
`bernstein_von_mises` ONLY if the diagonal-`Mseq` extraction resists — in that case close
`bernstein_von_mises_lintegral`, `scoreSum_uniformly_tight` and the whole of
`EfficientCentering.lean` from its statement.
