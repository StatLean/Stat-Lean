# bayes4-debt-gauss — close `gaussian_loss_convolution_continuous` [debt lane]

Branch `bay/debt-gauss`. The shared rules above apply. **Single target.**

## Touch-set (ONLY this file)

- `StatLean/AsymptoticStatistics/ForMathlib/MultivariateGaussianDensity.lean`

Gate: `lake build StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity`

## The one target

```
theorem gaussian_loss_convolution_continuous {S : Matrix ι ι ℝ} (hS : S.PosDef)
    {ℓ : EuclideanSpace ℝ ι → ℝ≥0∞} {p : ℝ} (hmeas : Measurable ℓ)
    (hpoly : ∀ h, ℓ h ≤ ENNReal.ofReal (1 + ‖h‖ ^ p)) (hp : 0 ≤ p) :
    Continuous fun u => ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian 0 S)
```

Everything else in this file is already closed and is available to you, in particular:

* `multivariateGaussian_eq_smul_withDensity hS` — `N(0,S) = c • volume.withDensity (fun x =>
  ofReal (exp (−⟪x, S⁻¹x⟫/2)))` with `0 < c ≠ ∞` (the normalizer is abstract);
* `gaussian_loss_convolution_lt_top` — the same integral is finite;
* `exists_forall_multivariateGaussian_le_smul_volume`,
  `exists_pos_smul_volume_le_multivariateGaussian`,
  `multivariateGaussian_compl_closedBall_uniform_small`,
  `multivariateGaussian_map_const_add`.

## Intended route (translate the `u`-dependence onto the smooth density)

1. Rewrite the integral against the density: by `multivariateGaussian_eq_smul_withDensity`
   and `lintegral_smul_measure` + `lintegral_withDensity_eq_lintegral_mul`,
   `∫⁻ z, ℓ(u − z) dN(0,S)(z) = c * ∫⁻ z, ℓ(u − z) * q z ∂volume` with
   `q z := ofReal (exp (−⟪z, S⁻¹z⟫/2))` continuous.
2. **Substitute `y := u − z`** to move `u` out of `ℓ` and into `q`. Lebesgue measure on
   `EuclideanSpace ℝ ι` is invariant under `z ↦ u − z` (translation + reflection):
   use `MeasureTheory.lintegral_sub_left_eq_self` / `Measure.IsNegInvariant` /
   `measurePreserving_sub_left`-style lemmas (loogle '"lintegral_sub_left"',
   '"IsAddLeftInvariant"', '"Measure.IsNegInvariant"'; `volume` on a finite-dim inner
   product space is an `addHaar` measure, hence both translation- and neg-invariant).
   Result: `∫⁻ y, ℓ y * q (u − y) ∂volume`.
3. Continuity in `u` by **dominated convergence**: for `uₙ → u`, the integrands
   `y ↦ ℓ y * q (uₙ − y)` converge pointwise (continuity of `q`) and are dominated, for `uₙ`
   in a fixed ball `‖uₙ‖ ≤ B`, by `y ↦ ℓ y * Q_B y` where
   `Q_B y := ofReal (exp (−(dist of y to the B-ball in the S⁻¹-quadratic form)²/2))`.
   Concretely: `⟪u − y, S⁻¹(u−y)⟫ ≥ λ‖u − y‖² ≥ λ(‖y‖ − B)²` for `‖u‖ ≤ B`, where
   `λ > 0` is a lower eigenvalue bound for `S⁻¹` — obtain it as
   `λ := ⨅ over the unit sphere` (compactness + PosDef; or use
   `Matrix.PosDef.le_smul`-style lemmas, loogle '"PosDef" "inner"' /
   '"PosDef.exists_pos"'). So the dominator is
   `y ↦ ofReal (1 + ‖y‖^p) * ofReal (exp (−λ(‖y‖ − B)²/2))`, which is integrable by the
   same argument that proves `gaussian_loss_convolution_lt_top` (reuse its private helpers
   if any, or redo: polynomial × Gaussian tail).
4. Use `Metric.continuous_iff` / sequential continuity
   (`continuous_iff_seqContinuous` on a metric space) plus
   `MeasureTheory.tendsto_lintegral_of_dominated_convergence`.

If step 3's eigenvalue bound is awkward, an alternative dominator avoids eigenvalues: on
`‖u‖ ≤ B`, `q (u − y) ≤ sup_{‖v‖ ≤ B} q(v − y)`, and since `q` is a decreasing function of
the quadratic form you may instead bound `q(u−y) ≤ q₀(y)` where
`q₀ y := ofReal (exp (−(max 0 (‖y‖ − B))² * λ / 2))`; same integrability argument.

## Done

Gate green, 0 sorries in this file. Report the route you used.
