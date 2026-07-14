import StatLean.NonparametricStatistics.Projection.MISEDecomposition
import StatLean.NonparametricStatistics.Projection.Aliasing

/-!
# MISE rate of the projection estimator over Sobolev classes

Over the Sobolev-ellipsoid class `{f = seriesFun θ : θ ∈ Θ(β, L²/π^{2β})}` (`β ≥ 1`), with
independent centered noise of common second moment `σ_ξ²` at the regular design, the
projection estimator of order `N = ⌈α·n^{1/(2β+1)}⌉` attains
$$ \sup_{f}\ \mathbb E\,\|\hat f_{nN} - f\|_{L^2[0,1]}^2 \;\le\; C\,n^{-\frac{2\beta}{2\beta+1}},
   \qquad C = C(\beta, L, \alpha, \sigma_\xi^2), $$
the same rate as for Hölder pointwise estimation — MISE-optimal over the class.

**Proof formalization notes.** Combine the exact decomposition (`proj_mise_decomposition`)
with the three term bounds: the stochastic term `σ_ξ²N/n ≤ σ_ξ²(α+1)·n^{−2β/(2β+1)}` (ceiling
bound `N ≤ αn^{1/(2β+1)} + 1`); the aliasing term
`∑_{j≤N} αⱼ² ≤ N·(residualConst β Q)²·n^{1−2β} = O(n^{1/(2β+1)+1−2β}) = O(n^{−2β/(2β+1)})`
for `β ≥ 1` (`riemannResidual_abs_le`); the tail `ρ_N ≤ Q/a_{N+1}² ≤ Q·N^{−2β}
≤ Q·α^{−2β}·n^{−2β/(2β+1)}` by the ellipsoid and monotonicity of the weights
(`a_{N+1} ≥ N^β`). Absolute summability of `θ` — the input of the decomposition — is derived
on the ellipsoid via `MemEllipsoid.summable_abs` (with `β ≥ 1 > 1/2`), never assumed. The
constant is existential with the stated dependence (binder position); side conditions
`3 ≤ n` and `N ≤ n − 1` hold for all large `n` and are explicit hypotheses of the finite-`n`
statement.

**Bibliographic comments.** Orthogonal-series rates over smoothness classes originate with
N. N. Čencov, *Soviet Math. Dokl.* **3** (1962), 1559–1562; the regular-design regression
form follows J. Rice, *Ann. Statist.* **12** (1984), 1215–1230, and R. Shibata, *Biometrika*
**68** (1981), 45–54; the ellipsoid viewpoint is standard since M. S. Pinsker, *Probl. Inf.
Transm.* **16** (1980), 120–133.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **MISE rate of the projection estimator over the Sobolev-ellipsoid class**: with
`N = ⌈α·n^{1/(2β+1)}⌉` there is `C = C(β, L, α, σ_ξ²)` such that for all admissible `n`,
every `θ ∈ Θ(β, L²/π^{2β})`, and every independent centered noise with second moment `σ_ξ²`,
`E‖f̂_{nN} − seriesFun θ‖₂² ≤ C·n^{−2β/(2β+1)}`. -/
theorem proj_sobolev_rate {β L α σξ2 : ℝ}
    -- USER-INPUT: smoothness at least one, positive radius and tuning, nonnegative noise
    -- level; classical parameters
    (hβ : 1 ≤ β) (hL : 0 < L) (hα : 0 < α) (hσ : 0 ≤ σξ2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n N : ℕ},
        -- LEAN-ONLY: side conditions valid for all large `n`; the finite-`n` form of the
        -- classical asymptotic statement
        3 ≤ n → N = ⌈α * (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1))⌉₊ → N ≤ n - 1 →
      ∀ {θ : ℕ → ℝ},
        MemEllipsoid β (ellipsoidRadius β L) θ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, ∫ ω, ξ i ω ∂P = 0) →
        (∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = ENNReal.ofReal σξ2) →
        ∫⁻ ω, (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
            ((projEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) N x
              - seriesFun θ x) ^ 2)) ∂P
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  sorry

end StatLean.NonparametricStatistics
