import StatLean.NonparametricStatistics.Projection.DiscreteOrthogonality
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mean and quadratic risk of trigonometric coefficient estimates

At the regular design with independent centered noise of common second moment `σ_ξ²`, the
coefficient estimates `θ̂ⱼ = n⁻¹∑ᵢYᵢφⱼ(xᵢ)` for the target `f = seriesFun θ` satisfy, for
`1 ≤ j ≤ n − 1`:
$$ \mathbb E[\hat\theta_j] = \theta_j + \alpha_j, \qquad
   \mathbb E[(\hat\theta_j - \theta_j)^2] = \frac{\sigma_\xi^2}{n} + \alpha_j^2, $$
where `αⱼ` is the Riemann-sum residual — the entire stochastic error is `σ_ξ²/n` *exactly*,
by discrete orthonormality.

Also here: elementary facts about `seriesFun` under absolute summability of the coefficients
(uniform bound, square-summability), used across the projection risk files.

**Proof formalization notes.** The mean is linearity plus `E ξᵢ = 0` (noise integrability is
*derived* from the second-moment equality: a finite `∫⁻ ξ²` forces `MemLp 2`, hence `L¹` on a
probability space). The variance uses independence to reduce to
`n⁻²∑ᵢ E ξᵢ²·φⱼ(xᵢ)² = (σ_ξ²/n)·(n⁻¹∑ᵢφⱼ(xᵢ)²)`, which is `σ_ξ²/n` by the diagonal case of
`trigBasis_discrete_orthonormal`. The `MSE` combines both with the cross term vanishing.

**Bibliographic comments.** J. Rice, *Ann. Statist.* **12** (1984), 1215–1230; the density
analogue of unbiased coefficient estimation is N. N. Čencov, *Soviet Math. Dokl.* **3**
(1962), 1559–1562.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Under absolute summability of the coefficients, the series function is uniformly bounded:
`|seriesFun θ x| ≤ √2·∑'|θⱼ|`. -/
theorem seriesFun_abs_le {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) (x : ℝ) :
    |seriesFun θ x| ≤ Real.sqrt 2 * ∑' j, |θ j| := by
  sorry

/-- Absolute summability of the coefficients implies square summability. -/
theorem summable_sq_of_summable_abs {θ : ℕ → ℝ} (hθ1 : Summable fun j => |θ j|) :
    Summable fun j => (θ j) ^ 2 := by
  sorry

/-- **Mean of the coefficient estimate**: `E[θ̂ⱼ] = θⱼ + αⱼ` for the target
`f = seriesFun θ` (any `j`; no index restriction is needed for the mean). -/
theorem coeffEstimator_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ} {θ : ℕ → ℝ} {σξ2 : ℝ} (j : ℕ)
    -- USER-INPUT: absolutely summable coefficients (so the target series converges); the
    -- classical summability assumption
    (hθ1 : Summable fun j => |θ j|)
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: centered noise; the fixed-design regression model
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    -- USER-INPUT: common noise second moment `σ_ξ²` (lower-Lebesgue form); the model
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = ENNReal.ofReal σξ2) :
    ∫ ω, coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j ∂P
      = θ j + riemannResidual θ n j := by
  sorry

/-- **Quadratic risk of the coefficient estimate**: for `1 ≤ j ≤ n − 1`,
`E[(θ̂ⱼ − θⱼ)²] = σ_ξ²/n + αⱼ²` — exactly. -/
theorem coeffEstimator_sq_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ} {θ : ℕ → ℝ} {σξ2 : ℝ} {j : ℕ}
    -- LEAN-ONLY: the index range in which discrete orthonormality holds
    (hj : 1 ≤ j) (hj' : j ≤ n - 1)
    -- USER-INPUT: nonnegative noise level; model parameter
    (hσ : 0 ≤ σξ2)
    -- USER-INPUT: absolutely summable coefficients; the classical summability assumption
    (hθ1 : Summable fun j => |θ j|)
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: mutually independent noise; the fixed-design regression model
    (hξi : iIndepFun ξ P)
    -- USER-INPUT: centered noise; the fixed-design regression model
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    -- USER-INPUT: common noise second moment `σ_ξ²` (lower-Lebesgue form); the model
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = ENNReal.ofReal σξ2) :
    ∫⁻ ω, ENNReal.ofReal
        ((coeffEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) j - θ j) ^ 2) ∂P
      = ENNReal.ofReal (σξ2 / n + (riemannResidual θ n j) ^ 2) := by
  sorry

end StatLean.NonparametricStatistics
