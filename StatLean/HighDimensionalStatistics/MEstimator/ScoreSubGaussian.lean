import StatLean.HighDimensionalStatistics.MEstimator.GLMDefs
import StatLean.HighDimensionalStatistics.ForMathlib.PsiTaylor
import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding

/-!
# Sub-Gaussianity of the GLM score (Wainwright Cor 9.26 proof, p. 288)

The probabilistic core of the GLM corollaries: each coordinate of the score
`∇Lₙ(θ*) = (1/n)∑ᵢ Vᵢ`, namely `scoreCoord M j = (1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ`, is sub-Gaussian with
variance proxy `≤ B²C²/n` under conditions (G1) (column normalization) and (G2) (the GLM exp-family
with `ψ'' ≤ B²`).

The per-term variable `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` has MGF `exp(ψ(ηᵢ+s) − ψ(ηᵢ) − s·ψ'(ηᵢ))`
(`s = −t·xᵢⱼ`) by the constitutive `hmgf` identity, which `psi_taylor_upper` bounds by `exp(B²xᵢⱼ²t²/2)` —
so `Vᵢⱼ` is centered sub-Gaussian with proxy `B²xᵢⱼ²`. Summing over the independent `i` and rescaling
by `1/n` (the `Lasso/RandomNoise.lean` `colInner_isSubGaussian` pattern) + (G1) gives proxy `B²C²/n`.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The per-term score variable `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is centered sub-Gaussian with proxy
`B²·xᵢⱼ²`. Derived from the constitutive MGF identity (`M.hmgf`) and `psi_taylor_upper`:
`mgf Vᵢⱼ μ t = exp(ψ(ηᵢ + (−t·xᵢⱼ)) − ψ(ηᵢ) − (−t·xᵢⱼ)·ψ'(ηᵢ)) ≤ exp(B²·xᵢⱼ²·t²/2)`. -/
theorem score_term_hasSubgaussianMGF (M : GLMExpFamily n d μ) (i : Fin n) (j : Fin d) :
    HasSubgaussianMGF (fun ω => (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j)
      ⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ μ := by
  sorry

/-- **GLM score coordinate sub-Gaussianity.** Under column normalization (G1, `IsColumnNormalized X C`)
and the GLM exp-family with `0 ≤ ψ'' ≤ B²` (G2, in `M`), the score coordinate
`scoreCoord M j = (1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is sub-Gaussian with variance proxy `B²C²/n`. -/
theorem score_coord_isSubGaussian (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : IsColumnNormalized M.X C) (hn : 0 < n) (j : Fin d) :
    IsSubGaussian (scoreCoord M j) ⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ μ := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
