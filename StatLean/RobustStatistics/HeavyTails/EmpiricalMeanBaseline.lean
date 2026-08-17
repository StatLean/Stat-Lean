import StatLean.RobustStatistics.LocationScale.Mean
import Mathlib.Probability.Moments.Variance

/-!
# The empirical-mean baseline — Chebyshev deviation under two moments

The starting point of modern (sub-Gaussian) mean estimation: under nothing but a finite
second moment, the deviation of the empirical mean is governed by Chebyshev's inequality
(`LM (2.3)`), and its `1/√δ` dependence on the confidence level — exponentially worse
than the `√log(1/δ)` a Gaussian sample would give (`LM (2.2)`) — is what every estimator
in this directory is built to beat.

* `sampleMean_variance` — `Var(μ̄ₙ) = σ²/n` for i.i.d. data with variance `σ²`.
* `sampleMean_chebyshev_deviation` — `P(|μ̄ₙ − μ| ≥ σ√(1/(nδ))) ≤ δ` (`LM (2.3)`).

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2, displays (2.1)–(2.3). The estimator is Round-1's `sampleMean`; Chebyshev is
Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq`.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **Variance of the empirical mean** (`LM §2`, the display `E(μ̄ₙ − μ)² = σ²/n`):
for i.i.d. square-integrable data the empirical mean has variance `σ²/n`. -/
theorem sampleMean_variance {n : ℕ} (hn : n ≠ 0) {X : Fin n → Ξ → ℝ} {μ₀ σ2 : ℝ}
    -- LEAN-ONLY: measurability of each coordinate; regularity implicit in LM §2
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are jointly independent; LM §2 ("i.i.d.")
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM §2 ("identically distributed draws from X")
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: P is square-integrable; LM (2.3) context ("if σ exists")
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM §2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) :
    ∫ ξ, (sampleMean (fun i => X i ξ) - μ₀) ^ 2 ∂μprob = σ2 / n := by
  sorry

/-- **Chebyshev's deviation bound for the empirical mean** (`LM (2.3)`): with probability
at least `1 − δ`, `|μ̄ₙ − μ| ≤ σ√(1/(nδ))`. The `1/√δ` confidence dependence is
essentially unimprovable for the empirical mean (`LM §2`, after (2.3), citing Catoni
(2012, Ann. IHP) Proposition 6.2) — the estimators of this directory replace it with
`√log(1/δ)`. -/
theorem sampleMean_chebyshev_deviation {n : ℕ} (hn : n ≠ 0) {X : Fin n → Ξ → ℝ}
    {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: measurability of each coordinate; regularity implicit in LM §2
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are jointly independent; LM §2
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM §2
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: P is square-integrable; LM (2.3) context
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM §2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: confidence level; LM (2.1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: nondegenerate variance (the bound is trivial at σ = 0); LM (2.3)
    (hσ : 0 < σ2) :
    μprob.real {ξ | Real.sqrt σ2 * Real.sqrt (1 / (n * δ))
      ≤ |sampleMean (fun i => X i ξ) - μ₀|} ≤ δ := by
  sorry

end StatLean.RobustStatistics
