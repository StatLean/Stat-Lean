# bayes4-debt-tight — close `bpe_tight` against the REPAIRED SeparatedLoss [debt lane]

Branch `bay/debt-tight`. The shared rules above apply. **Single target.**

## Touch-set (ONLY this file)

- `StatLean/Bayesian/BayesEstimators/Theorem10_8.lean`

Gate: `lake build StatLean.Bayesian.BayesEstimators.Theorem10_8`

## Background: the statement was FALSE and has been REPAIRED

A previous session correctly refused to prove `bpe_tight` and supplied a machine-checked
counterexample: the frozen `SeparatedLoss.strict` only required ONE pointwise pair
`ℓ x < ℓ y`, and under that reading the `0–1` loss is admissible, has zero sup–inf gap at
every scale, makes the posterior risk constant against an atomless posterior, and destroys
tightness.

**`Defs.lean` has since been repaired** (laptop-only surface) to vdV's genuine gap form:

```
strict : ∃ M : ℝ, 0 < M ∧ ∃ c : ℝ≥0∞,
  (∀ x, ‖x‖ ≤ M → ℓ x ≤ c) ∧ ∀ y, 2 * M ≤ ‖y‖ → c < ℓ y
```

i.e. `sup_{‖x‖ ≤ M} ℓ ≤ c < inf_{‖y‖ ≥ 2M} ℓ`. This is exactly the `η := ℓ̲(2δ) − ℓ̄(δ) > 0`
that vdV uses on p. 148. **`bpe_tight` is now provable — your job is to prove it.** Do not
alter any statement; if something still looks off, STOP and report precisely.

Everything else in the file is closed and available (do NOT redo):
`argmin_close_of_gap` (private, pointwise argmin consistency), `bayes_estimator_asymptotics`,
`bayes_estimator_weakConverges`, `gaussCriterion_argmin_zero_of_bowlShaped`,
`bayes_estimator_asymptotics_bowlShaped`.

Also available on your base (all 0-sorry, axiom-clean unless noted):
* `bernstein_von_mises`, `bernstein_von_mises_lintegral` (`Theorem10_1.lean`) — Thm 10.1;
* `scoreSum_uniformly_tight` (same file) — tightness of `Δₙ`;
* `posterior_tail_lintegral_tendsto` (`PosteriorTails.lean`) — display (10.9);
* `posteriorRisk_shifted_majorant`, `lintegral_loss_bvmGaussian` (`UniformApproximation.lean`);
* `bvmLocalPosterior_compl_ball`, `posterior_mass_compl_ball_tendsto`
  (`PosteriorConcentration.lean`);
* Gaussian bricks incl. `exists_pos_smul_volume_le_multivariateGaussian` (mean-uniform lower
  bound on balls) and `multivariateGaussian_compl_closedBall_uniform_small`.

## Intended route (vdV p. 148, Part 2)

Obtain `⟨M, hM, c, hle, hlt⟩ := hsep.strict`. Set `U := ball 0 M` (local scale) and let
`η` be the gap: for `x ∈ U` and `‖y‖ ≥ 2M`, `ℓ x ≤ c < ℓ y`. (Work in `ℝ≥0∞`; to get a
usable additive gap pick any `η > 0` with `c + η ≤ ℓ y` for all such `y` — e.g. from
`hlt` at a single `y₀` with `‖y₀‖ = 2M`, using `mono` to transfer to all `y`; mind that
`ℓ y` may be `∞`, which only helps.)

For `‖τ‖ ≥ 3M` and `h ∈ U`: `‖τ − h‖ ≥ ‖τ‖ − ‖h‖ ≥ 2M`, hence `ℓ(τ − h) > c ≥ ℓ(−h)`
(the latter since `‖−h‖ ≤ M`). Therefore, splitting the local posterior over
`U`, `Uᶜ ∩ C_n`, `C_nᶜ` with `C_n := ball 0 (Mseq n)` and `Mseq → ∞`:

```
Z_n(τ) − Z_n(0) ≥ η · Post(U) − ∫_{C_nᶜ} ℓ(−h) dPost
```
(on `Uᶜ ∩ C_n` the difference is `≥ 0` by `hsep.mono` at scale `Mseq n`, for `n` large
enough that `3M ≤ Mseq n`; be careful doing this subtraction in `ℝ≥0∞` — it is cleaner to
prove the equivalent additive form `Z_n(0) + η·Post(U) ≤ Z_n(τ) + tail_n` and avoid `tsub`).

Then:
* `Post(U)` is bounded below by a deterministic `p₀ > 0` with probability → 1: compare with
  `N(Δₙ, J⁻¹)(U)` using `bernstein_von_mises` (TV bound on the measurable set `U`), and bound
  that below by `exists_pos_smul_volume_le_multivariateGaussian` on the event
  `‖Δₙ‖ ≤ K` from `scoreSum_uniformly_tight`;
* `tail_n → 0` in probability by `posterior_tail_lintegral_tendsto` (10.9) with the envelope
  `1 + ‖h‖^p ≥ ℓ(−h)` from `hpoly`.

On the good event, `hT` at `t := 0` forces `Z_n(√n(Tₙ−θ₀)) ≤ Z_n(0) + εₙ`, which is
incompatible with `‖√n(Tₙ−θ₀)‖ ≥ 3M` once `εₙ + tail_n < η·p₀`. Hence
`P(‖√n(Tₙ−θ₀)‖ ≥ 3M) → 0`, and the required `∃ K` form follows with `K := 3M` (any `ε` is
absorbed by taking `n` large; note the conclusion is `∀ᶠ n`, so you do NOT need a uniform-in-`n`
statement for small `n`).

## Done

Gate green, 0 sorries in the file, and `#print axioms StatLean.Bayesian.bpe_tight` shows only
`[propext, Classical.choice, Quot.sound]`. Report the gap constant you used.
