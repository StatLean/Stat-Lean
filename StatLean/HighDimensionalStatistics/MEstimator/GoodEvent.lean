import StatLean.HighDimensionalStatistics.MEstimator.ScoreSubGaussian
import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.ConcentrationInequalities.SubGaussian.TailBounds

/-!
# High-probability good event for the GLM score (Wainwright Cor 9.26 proof, p. 288)

The probabilistic step that discharges the deterministic "good event" `𝔾(λ) = {Φ*(∇Lₙ(θ*)) ≤ λ/2}`
for the `ℓ₁`-regularized GLM. Since `Φ* = ℓ∞` and `∇Lₙ(θ*) = scoreVec`, the good event is
`{‖scoreVec‖∞ ≤ λ/2}`. A two-sided sub-Gaussian tail on each coordinate (`score_coord_isSubGaussian`,
proxy `B²C²/n`) + a union bound over the `d` coordinates gives
`P(‖scoreVec‖∞ > t) ≤ 2d·exp(−t²/(2B²C²/n))`; choosing `λ = 4BC{√(log d/n) + δ}` and `t = λ/2` makes
this `≤ 2exp(−2nδ²)`. Structurally identical to `Lasso/RandomNoise.lean` (`linfNorm_noise_tail` +
the good-event split of `lasso_random_rate`).
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Coordinate of the score vector.** `(scoreVec M ω).ofLp j = scoreCoord M j ω`. -/
theorem scoreVec_ofLp (M : GLMExpFamily n d μ) (ω : Ω) (j : Fin d) :
    (scoreVec M ω).ofLp j = scoreCoord M j ω := by
  sorry

/-- **Union-bound tail on `‖scoreVec‖∞`** (Wainwright Cor 9.26 proof). For each coordinate the score is
sub-Gaussian with proxy `B²C²/n` (`score_coord_isSubGaussian`); a two-sided tail + union bound over the
`d` coordinates gives `P(‖scoreVec‖∞ > t) ≤ 2d·exp(−t²/(2·B²C²/n))`. (The `linfNorm_noise_tail` pattern.) -/
theorem score_linfNorm_tail (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    -- USER-INPUT: column normalization (G1); Wainwright §9.5 (G1).
    (C : ℝ) (hC : IsColumnNormalized M.X C)
    -- USER-INPUT: positive sample size; Wainwright Cor 9.26.
    (hn : 0 < n)
    -- USER-INPUT: positive variance proxy; needed for the tail (degenerate otherwise).
    (hσ : 0 < M.B ^ 2 * C ^ 2 / n)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | t < linfNorm (scoreVec M ω)} ≤
      ENNReal.ofReal (2 * d * Real.exp (-t ^ 2 / (2 * (M.B ^ 2 * C ^ 2 / n)))) := by
  sorry

/-- **High-probability good event** (Wainwright Cor 9.26). With `λ = 4BC{√(log d/n) + δ}` (or larger),
`P(‖scoreVec‖∞ ≤ λ/2) ≥ 1 − 2·exp(−2nδ²)`. Setting `t = λ/2` in `score_linfNorm_tail`, the bound
`2d·exp(−nt²/(2B²C²))` simplifies to `2·exp(−2nδ²)` via `(a+b)² ≥ a²+b²` and `d ≥ 1`. -/
theorem good_event_highProb (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : IsColumnNormalized M.X C)
    -- USER-INPUT: positive sample size; Wainwright Cor 9.26.
    (hn : 0 < n)
    -- USER-INPUT: `d ≥ 1` (for `log d ≥ 0` and the union bound); Wainwright Cor 9.26.
    (hd : 0 < d)
    -- USER-INPUT: confidence offset `δ ∈ (0,1)`; Wainwright Cor 9.26.
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    -- USER-INPUT: positive cumulant/normalization constants `B, C`; Wainwright §9.5 (G1/G2).
    (hB : 0 < M.B) (hCpos : 0 < C)
    (lam : ℝ)
    -- USER-INPUT: tuning `λ ≥ 4BC{√(log d/n) + δ}`; Wainwright Cor 9.26.
    (hlam : 4 * M.B * C * (Real.sqrt (Real.log d / n) + δ) ≤ lam) :
    ENNReal.ofReal (1 - 2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)) ≤
      μ {ω | linfNorm (scoreVec M ω) ≤ lam / 2} := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
