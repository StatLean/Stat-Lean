import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Empirical-Bayes (Bayes) risk of the shrinkage estimator — assembly

The Gaussian sequence model with a Gaussian prior (Candès, Lecture 15, §15.3.3, STAT 300C):
prior `θᵢ ∼ N(0, τ²)`, noise `εᵢ ∼ N(0, σ²)` with `θᵢ ⟂ εᵢ`, observed data `Xᵢ = θᵢ + εᵢ`. The
Bayes estimator (posterior mean) shrinks the data by `s = τ²/(σ²+τ²)`:
`μ̂_B,ᵢ = s · Xᵢ = (τ²/(σ²+τ²))·(θᵢ+εᵢ)` (Eq. 15.3).

**Main result** (`empiricalBayes_risk`, Candès L15 §15.3.3, Proposition 1): the Bayes risk is the
MLE risk shrunk by `τ²/(σ²+τ²)`:
`E‖μ̂_B − θ‖² = (p·σ²)·τ²/(σ²+τ²) = R_MLE · τ²/(σ²+τ²)`, with `R_MLE = E‖X − θ‖² = p·σ²`.

*Proof.* Per coordinate, the residual is `μ̂_B,ᵢ − θᵢ = (s−1)θᵢ + s·εᵢ = −ρ·θᵢ + s·εᵢ`
(`ρ = 1−s = σ²/(σ²+τ²)`). By independence and `E[θᵢ]=E[εᵢ]=0`, the cross term vanishes, so
`E[(μ̂_B,ᵢ−θᵢ)²] = ρ²·E[θᵢ²] + s²·E[εᵢ²] = ρ²τ² + s²σ² = σ²τ²/(σ²+τ²)`; sum over the `p`
coordinates. (`E[θᵢ²] = τ²`, `E[εᵢ²] = σ²` are the Gaussian second moments `= variance + mean²`.)
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Empirical-Bayes / Bayes risk of the Gaussian shrinkage estimator** (Candès, Lecture 15,
§15.3.3, Proposition 1, STAT 300C). For a Gaussian prior `θᵢ ∼ N(0,τ²)` and independent noise
`εᵢ ∼ N(0,σ²)`, the shrinkage estimator `μ̂_B,ᵢ = (τ²/(σ²+τ²))·(θᵢ+εᵢ)` has Bayes risk
`E‖μ̂_B − θ‖² = p·σ²τ²/(σ²+τ²)` ( `= R_MLE · τ²/(σ²+τ²)`, `R_MLE = pσ²`). -/
theorem empiricalBayes_risk {p : ℕ} {σ2 τ2 : ℝ} (hσ : 0 < σ2) (hτ : 0 < τ2)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (θ ε : Fin p → Ω → ℝ)
    -- USER-INPUT: each prior coordinate is measurable; Candès L15 §15.3.3
    (hθmeas : ∀ i, Measurable (θ i))
    -- USER-INPUT: each noise coordinate is measurable; Candès L15 §15.3.3
    (hεmeas : ∀ i, Measurable (ε i))
    -- USER-INPUT: prior θᵢ ∼ N(0, τ²); Candès L15 §15.3.3
    (hθlaw : ∀ i, Measure.map (θ i) μ = gaussianReal 0 ⟨τ2, hτ.le⟩)
    -- USER-INPUT: noise εᵢ ∼ N(0, σ²); Candès L15 §15.3.3
    (hεlaw : ∀ i, Measure.map (ε i) μ = gaussianReal 0 ⟨σ2, hσ.le⟩)
    -- USER-INPUT: prior and noise are independent within each coordinate; Candès L15 §15.3.3
    (hindep : ∀ i, IndepFun (θ i) (ε i) μ) :
    (∫ ω, ∑ i, ((τ2 / (σ2 + τ2)) * (θ i ω + ε i ω) - θ i ω) ^ 2 ∂μ)
      = (p : ℝ) * (σ2 * τ2 / (σ2 + τ2)) := by
  sorry

end StatLean.MultipleTesting
