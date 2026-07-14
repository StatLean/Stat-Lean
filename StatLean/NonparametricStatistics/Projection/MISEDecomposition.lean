import StatLean.NonparametricStatistics.Projection.CoefficientRisk
import StatLean.NonparametricStatistics.Projection.TrigOrthogonality

/-!
# Exact MISE decomposition of the projection estimator

At the regular design with independent centered noise of common second moment `σ_ξ²`, for the
target `f = seriesFun θ` and any order `1 ≤ N ≤ n − 1`:
$$ \mathbb E\,\|\hat f_{nN} - f\|_{L^2[0,1]}^2
   \;=\; \frac{\sigma_\xi^2 N}{n} \;+\; \sum_{j=1}^N \alpha_j^2 \;+\; \rho_N,
   \qquad \rho_N = \sum_{j>N}\theta_j^2 $$
— an exact identity: stochastic error `σ_ξ²N/n`, Riemann-sum (aliasing) error `∑αⱼ²`, and
approximation (tail) error `ρ_N`.

**Proof formalization notes.** Expand `f̂ − f = ∑_{j≤N}(θ̂ⱼ − θⱼ)φⱼ − ∑_{j>N}θⱼφⱼ`. The `L²`
cross terms vanish and the squares decouple by orthonormality (`trigBasis_orthonormal`); the
tail's squared norm is `ρ_N` by dominated convergence (uniform convergence of the tail series
under `∑|θ| < ∞`, envelope `(√2·∑|θ|)²` on the finite interval) plus orthonormality — no
completeness of the trigonometric system is invoked, since `f` is *defined* by its series.
Then take expectations termwise (`coeffEstimator_sq_error` for `j ≤ N`; independence kills
the `j ≠ k` covariance terms via the mean formula). Everything is stated in `∫⁻` form.

**Bibliographic comments.** The exact decomposition is the standard starting point of
orthogonal-series risk analysis: N. N. Čencov, *Soviet Math. Dokl.* **3** (1962), 1559–1562;
J. Rice, *Ann. Statist.* **12** (1984), 1215–1230.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Exact MISE decomposition of the projection estimator**: for `1 ≤ N ≤ n − 1`,
`E‖f̂_{nN} − f‖₂² = σ_ξ²·N/n + ∑_{j≤N} αⱼ² + ρ_N` with `f = seriesFun θ`. -/
theorem proj_mise_decomposition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n N : ℕ} {ξ : Fin n → Ω → ℝ} {θ : ℕ → ℝ} {σξ2 : ℝ}
    -- LEAN-ONLY: order range in which discrete orthonormality applies
    (hN : 1 ≤ N) (hN' : N ≤ n - 1)
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
    ∫⁻ ω, (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
        ((projEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) N x
          - seriesFun θ x) ^ 2)) ∂P
      = ENNReal.ofReal (σξ2 * N / n
          + (∑ j ∈ Finset.Icc 1 N, (riemannResidual θ n j) ^ 2) + tailEnergy θ N) := by
  sorry

end StatLean.NonparametricStatistics
