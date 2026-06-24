Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools HARD (this is Gaussian
analysis; many bricks exist in Mathlib). Never `lake update`. You are inside an srun allocation —
build with plain `lake build`, ITERATE. This is the hardest unit; budget time, prove carefully.

# CONTEXT
`StatLean/HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean`
(namespace `StatLean.HighDimensionalStatistics`; `open MeasureTheory ProbabilityTheory Matrix`,
`open scoped ENNReal NNReal`, `open StatLean.ConcentrationInequalities`; `variable {n d : ℕ}`)
has TWO theorems `:= by sorry`. It imports:
* `AsymptoticStatistics/ForMathlib/GaussianMGF.lean` — provides (READ IT) `mgf_gaussianReal`,
  `integral_exp_mul_gaussianReal`, `integral_exp_inner_stdGaussian`,
  `integral_exp_inner_multivariateGaussian`, and `multivariateGaussian_map_inner_eq_gaussianReal`
  (`Measure.map ⟪h,·⟫ (multivariateGaussian 0 J) = gaussianReal 0 (h·J·h)`-style).
* `ConcentrationInequalities/SubExponential/Defs.lean` — `IsSubExponential X α μ` is a structure with
  fields `mgf_le : ∀ l, |l| ≤ 1/α → mgf (fun ω => X ω − ∫ x, X x ∂μ) μ l ≤ exp(l²α²/2)` and
  `integrable_exp_mul : ∀ l, |l| ≤ 1/α → Integrable (fun ω => exp(l·(X ω − ∫ x, X x ∂μ))) μ`.
* `ConcentrationInequalities/SubExponential/SampleMean.lean` — the i.i.d. sub-exponential sample-mean
  tail. READ IT for the exact name/shape (e.g. `measure_sampleMean_lt_le_quadratic`/`_linear`); it is
  the engine for the second theorem.
* `LinearModel/Defs.lean` — `designMap X : E^d →ₗ E^n`, `β ↦ Xβ`.

# TASK — close BOTH theorems to 0-sorry.

## (1) `chiSq1_centered_isSubExponential` : for `g ∼ N(0,1)`, `g²−1` is sub-exponential, `α = 4`.
First, `∫ ω, (g ω ^2 − 1) ∂μ = 0`: `E[g²] = 1` since `Measure.map g μ = gaussianReal 0 1` and
`∫ x, x^2 ∂gaussianReal 0 1 = variance = 1` (search `'"variance_gaussianReal"'`,
`'"integral_id_gaussianReal"'`, `'"integral_fun_gaussianReal"'`; or via `integral_map hg_meas`).
So the centered variable equals `g²−1` and `mgf (g²−1) μ l = ∫ exp(l(g²−1)) ∂μ`.
- **Closed-form MGF.** `∫ exp(l(g²−1)) ∂μ = e^{−l} ∫ exp(l·g²) ∂μ = e^{−l} ∫ exp(l x²) ∂gaussianReal 0 1`
  (`integral_map hg_meas`). Compute `∫ exp(l x²) ∂gaussianReal 0 1 = (1−2l)^{-1/2}` for `l < 1/2`:
  unfold the measure to its density (`gaussianReal` is `volume.withDensity (gaussianPDFReal 0 1)` for
  variance ≠ 0; search `'"gaussianReal"' '"withDensity"'`, `'"gaussianPDFReal"'`,
  `'"integral_gaussianPDFReal"'`), then `∫ (1/√(2π)) exp(−x²/2) exp(l x²) = (1/√(2π)) ∫ exp(−(1/2−l)x²)`,
  and `∫ exp(−b x²) = √(π/b)` is Mathlib `integral_gaussian` (b = 1/2 − l > 0). Result
  `√(π/(1/2−l))/√(2π) = (1−2l)^{-1/2}`.
- **MGF field.** Show `e^{−l}(1−2l)^{-1/2} ≤ exp((l²·16)/2) = exp(8 l²)` for `|l| ≤ 1/4`. It suffices to
  prove the sharper `e^{−l}(1−2l)^{-1/2} ≤ exp(2 l²)` on `|l| ≤ 1/4` (then `2l² ≤ 8l²`). Take logs:
  reduce to `−l − (1/2)·log(1−2l) ≤ 2 l²` for `l ∈ [−1/4, 1/4]` (so `1−2l ∈ [1/2, 3/2]`). Prove with
  `Real.log` bounds: `−log(1−2l) ≤ 2l + 4l²` on this range (from `Real.log_le_sub_one_of_pos` applied to
  `1/(1−2l)`, or `Real.add_one_le_exp`/Taylor + `nlinarith`). Time-box the sharp constant: if `2l²` is
  awkward, `8l²` is the actual requirement and is looser — aim straight for `8 l²` with `nlinarith`
  given `log` bounds. **If after real effort the clean `α = 4` constant resists, you MAY pick a larger
  `α` (smaller range `1/α`, looser bound) — but then the second theorem's exponent changes; KEEP the
  two theorems mutually consistent and document the constant.**
- **integrable_exp_mul field.** `Integrable (fun ω => exp(l(g²−1))) μ` for `|l|≤1/4`: by
  `integrable_map_measure`/`hg` it equals integrability of `x ↦ e^{−l}exp(l x²)` under `gaussianReal 0 1`,
  finite since `l < 1/2` (the Gaussian integral above is finite). Search `'"Integrable"' '"gaussianReal"'`,
  `'"integrable_exp"' '"gaussian"'`.

## (2) `gaussian_quadratic_form_tail` : `P(|‖Xβ‖²/‖β‖² − 1| > δ) ≤ 2 exp(−n δ²/8)`.
Reduce to the χ² sample mean. For each row `i`, `(designMap (X ω) β).ofLp i = ∑ⱼ X ω i j · β.ofLp j`
is a linear combination of the independent `N(0,1/n)` entries, hence `∼ N(0, ‖β‖²/n)`. Set
`g i ω := (Real.sqrt n / ‖β‖) · (designMap (X ω) β).ofLp i`; then `g i ∼ N(0,1)`, the `g i` are
independent (row independence from `hindep`), and
`‖designMap (X ω) β‖² / ‖β‖² = (1/n) ∑ᵢ (g i ω)²` (`EuclideanSpace.norm_sq_eq`/`norm_eq`, algebra).
Two routes for the law `g i ∼ N(0,1)`:
  (a) coordinatewise: sum of independent Gaussians is Gaussian — `gaussianReal_add_gaussianReal_of_indepFun`
      + scaling `gaussianReal_map_const_mul`/`gaussianReal_map_mul_const`, by induction over `Finset.univ`
      (template: `Lasso/RandomNoise.lean::colInner_isSubGaussian` does the sub-Gaussian analogue with
      `iIndepFun` + `HasSubgaussianMGF.sum_of_iIndepFun`); OR
  (b) identify the row law as `multivariateGaussian 0 ((1/n)·1)` and apply
      `multivariateGaussian_map_inner_eq_gaussianReal` from `GaussianMGF.lean`.
Then `Zᵢ := (g i)² − 1` is sub-exponential (`α=4`) by theorem (1), i.i.d. mean-0, and the event
`{|‖Xβ‖²/‖β‖² − 1| > δ} = {|(1/n)∑ᵢ Zᵢ| > δ}`. Apply the SampleMean sub-exponential tail (two-sided:
apply to `Zᵢ` and `−Zᵢ`, add) to get `≤ 2 exp(−n δ²/(2α²))`. With `α=4` this is `2 exp(−nδ²/32)`; the
stub writes `/8` (book eq:fix-b, sharp `α=2`). **State the PROVABLE exponent** — change the `8` in the
conclusion to the constant you actually prove (e.g. `32`) and DOCUMENT the deviation in the docstring
(CLAUDE.md §1). `δ ≤ 1 ≤ α` keeps you in the quadratic regime. REPORT the final exponent constant
clearly — the downstream RandomRIP unit needs it.

# REQUIREMENTS
ZERO sorry. Keep both theorem names and the hypotheses/tags. You may change the conclusion CONSTANT of
theorem (2) to the provable value (documented) and may add private helper lemmas in this file. Search
before reproving: many Gaussian-integral/variance facts are in Mathlib.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.CompressedSensing.GaussianChiSquared
# DONE = build exits 0; 0 sorries; commit
  (`cs(chisq): centered chi-sq1 sub-exponential + fixed-beta quadratic-form tail (Lu-BDA ch7)`).
  Report: build status, sorry count, the proved `α`, the FINAL exponent constant in theorem (2), and
  the Mathlib lemmas used for the Gaussian integral / sum-of-Gaussians law.
