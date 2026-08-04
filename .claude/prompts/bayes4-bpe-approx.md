# bayes4-bpe-approx — uniform approximation of the recentred posterior risk [wave 3]

Branch `bay/bpe-approx`. The shared rules above apply.

## Touch-set (ONLY this file)

- `StatLean/Bayesian/BayesEstimators/UniformApproximation.lean`

Gate: `lake build StatLean.Bayesian.BayesEstimators.UniformApproximation`

Available on your base branch (closed earlier — trust the statements):
- `bernstein_von_mises` and `bernstein_von_mises_lintegral` (`Theorem10_1.lean`);
- `posterior_tail_lintegral_tendsto` — display (10.9), the polynomial-weighted posterior
  tail (`PosteriorTails.lean`);
- TV toolbox incl. `lintegral_le_lintegral_add_tvDist`
  (`∫ w dμ ≤ ∫ w dν + B · tvDist μ ν` for `w ≤ B` measurable) and `tvDist_le_one`;
- Gaussian bricks: `multivariateGaussian_map_const_add`,
  `gaussian_loss_convolution_lt_top`, `gaussian_loss_convolution_continuous`,
  `multivariateGaussian_compl_closedBall_uniform_small`;
- `scoreSum_uniformly_tight` (`Theorem10_1.lean`) for `‖Δₙ‖`-tightness.

## Targets

### `lintegral_loss_bvmGaussian`
`∫⁻ h, ℓ(t − h) dN(Δₙ, J⁻¹) = bpeGaussCriterion J ℓ (t − Δₙ)`.
Route: `bvmGaussian = N(Δₙ, J⁻¹) = (N(0,J⁻¹)).map (Δₙ + ·)` by
`multivariateGaussian_map_const_add`; then `lintegral_map` (measurable `ℓ` and the
translation) turns the left side into `∫⁻ z, ℓ(t − (Δₙ + z)) dN(0,J⁻¹)`; rewrite
`t − (Δₙ + z) = (t − Δₙ) − z` (`sub_add_eq_sub_sub`) — that is exactly
`bpeGaussCriterion J ℓ (t − Δₙ)`.

### `posteriorRisk_shifted_majorant` (the lane's main work)
Build a measurable majorant `Mn n ω` dominating, uniformly over `‖τ‖ ≤ R`, both
`Zₙ(τ + Δₙ) − g(τ)` and `g(τ) − Zₙ(τ + Δₙ)`.

Suggested explicit majorant (all three terms are measurable in `ω` and τ-free):
```
Mn n ω := B_{R,n} * bvmTV κ π θ₀ J sc n ω                      -- truncated TV term
        + ∫⁻ h in (ball 0 (S n))ᶜ, ofReal (1 + ‖h‖^p) ∂(localPosterior n ω)  -- (10.9)
        + ∫⁻ h in (ball 0 (S n))ᶜ, ofReal (1 + ‖h‖^p) ∂(bvmGaussian J sc n ω) -- Gauss tail
```
with a truncation radius sequence `S n → ∞` (choose `S n := Mseq n` from (10.9), or simply
`S n := n`) and `B_{R,n} := ofReal (1 + (R + S n)^p)` the sup of the loss envelope on the
truncation ball (from `hpoly`: for `‖τ‖ ≤ R` and `‖h‖ ≤ S n`, `ℓ(τ + Δₙ − h)` is NOT
bounded by that — CAREFUL: the argument is `τ + Δₙ − h`, which involves `Δₙ`. Two options:
(i) include `‖Δₙ‖` in the envelope: `B := ofReal (1 + (R + ‖Δₙ ω‖ + S n)^p)` (still
measurable in `ω`, τ-free) — then the TV term is `B(ω) · tvDist`, which →ᵖ 0 because
`tvDist →ᵖ 0` (BvM) and `B` is tight (`scoreSum_uniformly_tight`); product of a
tight sequence and an in-probability-null sequence is in-probability null (prove as a
`private` lemma: `∀ δ, P{B·T ≥ δ} ≤ P{B > K} + P{T ≥ δ/K}`).
(ii) recentre first: substitute `h' := h − Δₙ` on BOTH measures — the local posterior
recentred and `N(0,J⁻¹)` — which removes `Δₙ` from the loss argument entirely but moves it
into the integrator. Option (i) is more mechanical; prefer it.)

Per-τ estimate (for `‖τ‖ ≤ R`), both directions:
```
Zₙ(τ+Δₙ) = ∫⁻ ℓ(τ+Δₙ−h) d(localPost)
         = ∫⁻_{ball} … + ∫⁻_{ballᶜ} …
   ≤ (∫⁻_{ball} … d(gauss) + B·tvDist) + tail_post      -- lintegral_le_lintegral_add_tvDist
   ≤ ∫⁻ ℓ(τ+Δₙ−h) d(gauss) + B·tvDist + tail_post
   = g(τ) + B·tvDist + tail_post                         -- lintegral_loss_bvmGaussian
```
and symmetrically with `tail_gauss` on the other side. Note
`lintegral_le_lintegral_add_tvDist` applies to the **restricted** integrands
`w := ℓ(τ+Δₙ−·) · 1_{ball}` (measurable, bounded by `B`); the restriction to the ball is
what makes them bounded. Then `Mn` is the sum of the three τ-free bounds.

Vanishing in probability: TV term by `bernstein_von_mises` + tightness (as above);
`tail_post` by `posterior_tail_lintegral_tendsto` (choose `S n` = its `Mseq`);
`tail_gauss` by the Gaussian tail bricks — `∫⁻_{‖h‖ ≥ S n} (1+‖h‖^p) dN(Δₙ,J⁻¹) → 0`
uniformly on `{‖Δₙ‖ ≤ K}`: prove a `private` lemma from
`gaussian_loss_convolution_lt_top` (finiteness) + dominated convergence over the shrinking
tails, or bound by `multivariateGaussian_compl_closedBall_uniform_small` after splitting
the polynomial weight with Cauchy–Schwarz/`ENNReal` Hölder. If uniformity is painful,
integrate the weight against the translated Gaussian and use monotone convergence with the
`ω`-independent envelope after recentring by `Δₙ` (the recentred measure is `N(0,J⁻¹)`,
`ω`-free!) — this is the clean route: `∫⁻_{‖h‖≥S} (1+‖h‖^p) dN(Δₙ,J⁻¹) =
∫⁻_{‖z+Δₙ‖≥S} (1+‖z+Δₙ‖^p) dN(0,J⁻¹) ≤ ∫⁻_{‖z‖≥S−K} (1+(‖z‖+K)^p) dN(0,J⁻¹)` on
`{‖Δₙ‖ ≤ K}`, and the right side is a deterministic sequence → 0 (dominated convergence,
finite by `gaussian_loss_convolution_lt_top`).

Measurability of `Mn n`: TV term (`measurable_tvDist_kernel` + `measurable_bvmEffScore`);
tail terms (`Kernel.measurable_lintegral`-style on the posterior kernel and on the Gaussian
kernel packaging used in `Theorem10_1.lean`).

## Done

Gate green. Report closed/left. Sanctioned NAMED DEBT: none — this lane must close both
targets (it is the last input to Theorem 10.8).
