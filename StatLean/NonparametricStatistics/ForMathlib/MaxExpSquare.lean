import StatLean.NonparametricStatistics.ForMathlib.GaussianExpSq

/-!
# Maximal inequalities via exponential-square moments

* `lintegral_iSup_sq_le_log` — if `E[exp(α₀·ηⱼ²)] ≤ C₀` for `j = 1, …, M`, then
  `E[max_j ηⱼ²] ≤ log(C₀·M)/α₀`. No independence is required.
* `lintegral_iSup_normSq_gaussian_le` — for `M` random vectors in `ℝ^d` whose coordinates are
  centered Gaussians with variances `≤ vmax`:
  `E[max_j ‖ηⱼ‖²] ≤ 4·d·vmax·log(√2·M·d)`.

These are the grid-maximum bounds behind sup-norm risk rates of linear smoothers with Gaussian
noise (the `log n` price of the sup-norm).

**Proof formalization notes.** The first bound is Jensen + a union bound inside the logarithm:
`E max ηⱼ² = α₀⁻¹·E log max exp(α₀ηⱼ²) ≤ α₀⁻¹·log E ∑ⱼ exp(α₀ηⱼ²) ≤ α₀⁻¹·log(M·C₀)`.
Note `C₀ ≥ 1` is *derived* (each `E exp(α₀η²) ≥ 1` by Jensen since `E[α₀η²] ≥ 0`), not
assumed. The vector corollary takes `α₀ = 1/(4·vmax)`, applies the Gaussian
exponential-square bound `≤ √2` coordinatewise (`M·d` scalar variables), and uses
`max_j ∑_k η_{jk}² ≤ d·max_{j,k} η_{jk}²`.

**Bibliographic comments.** The `log M` maximal bound from uniform exponential moments is a
classical device in Gaussian process theory and nonparametric sup-norm analysis; see e.g.
W. Härdle, *Applied Nonparametric Regression* (Cambridge, 1990) and standard references on
maxima of Gaussian vectors.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Maximal bound from exponential-square moments**: if `E[exp(α₀·ηⱼ²)] ≤ C₀` for each of
the `M ≥ 1` (arbitrarily dependent) variables `ηⱼ`, then
`E[max_j ηⱼ²] ≤ log(C₀·M)/α₀`. -/
theorem lintegral_iSup_sq_le_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M : ℕ}
    -- LEAN-ONLY: at least one variable, so the maximum is over a nonempty family
    (hM : 1 ≤ M)
    {η : Fin M → Ω → ℝ} {α₀ C₀ : ℝ}
    -- USER-INPUT: positive exponent scale; classical input of the maximal bound
    (hα : 0 < α₀)
    -- LEAN-ONLY: measurability of the variables; standard regularity
    (hmeas : ∀ j, Measurable (η j))
    -- USER-INPUT: uniform exponential-square moment bound; classical input
    (hexp : ∀ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (α₀ * (η j ω) ^ 2)) ∂P
      ≤ ENNReal.ofReal C₀) :
    ∫⁻ ω, ENNReal.ofReal (⨆ j, (η j ω) ^ 2) ∂P
      ≤ ENNReal.ofReal (Real.log (C₀ * M) / α₀) := by
  sorry

/-- **Expected maximum of squared norms of Gaussian-coordinate vectors**: if each coordinate
`η j · k` of the `M ≥ 1` random vectors in `ℝ^d` (`d ≥ 1`) is a centered Gaussian with
variance at most `vmax`, then `E[max_j ‖ηⱼ‖²] ≤ 4·d·vmax·log(√2·M·d)`.
No independence (within or across vectors) is required. -/
theorem lintegral_iSup_normSq_gaussian_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M d : ℕ}
    -- LEAN-ONLY: nonempty family and nonzero dimension
    (hM : 1 ≤ M) (hd : 1 ≤ d)
    {η : Fin M → Ω → Fin d → ℝ} {vmax : ℝ≥0}
    -- LEAN-ONLY: measurability of the coordinates; standard regularity
    (hmeas : ∀ j k, Measurable fun ω => η j ω k)
    -- USER-INPUT: each coordinate is a centered Gaussian with variance at most `vmax`;
    -- classical Gaussian-vector input
    (hgauss : ∀ j k, ∃ v : ℝ≥0, v ≤ vmax ∧ HasLaw (fun ω => η j ω k) (gaussianReal 0 v) P) :
    ∫⁻ ω, ENNReal.ofReal (⨆ j, ∑ k, (η j ω k) ^ 2) ∂P
      ≤ ENNReal.ofReal (4 * d * (vmax : ℝ) * Real.log (Real.sqrt 2 * M * d)) := by
  sorry

end StatLean.NonparametricStatistics
