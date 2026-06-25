import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Theorem7_21
import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.TailBounds
import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
import Mathlib.Probability.Independence.Basic

/-!
# Corollary 7.22 — Lasso support recovery under sub-Gaussian noise (Wainwright §7.5)

The probabilistic specialization of Theorem 7.21: with i.i.d. zero-mean σ-sub-Gaussian noise,
the C-column-normalization condition, and the explicit regularization choice (7.46)
`λₙ = (2Cσ/(1−α))(√(2log(d−s)/n) + δ)`, the support-recovery guarantees hold with probability
at least `1 − 4e^{−nδ²/2}`, with the ℓ∞ bound (7.47).

Proof shell (mirrors `Lasso/RandomNoise.lean`): the two random max-terms of (7.45)/(7.44) —
`‖Xₛᶜᵀ Π_{S⊥}(X) w/n‖_∞` (max over `d−s` coordinates, each sub-Gaussian with proxy `≤ C²σ²/n`
via projection contractivity + column normalization) and `‖(XₛᵀXₛ/n)⁻¹ Xₛᵀ w/n‖_∞` (max over
`s` coordinates, each sub-Gaussian with proxy `≤ σ²/(c_min n)` via the inverse-Gram operator
bound) — are controlled by the maximal inequality `tail_max_le`; the `λ` choice (7.46) makes
the regularization condition (7.44) hold, and a union bound gives `4e^{−nδ²/2}`. On the good
event, Theorem 7.21 (a)–(c) gives uniqueness, `supp ⊆ S`, and the bound (7.47).

Reuses: `IsSubGaussian`, `isSubGaussian_const_mul`, `HasSubgaussianMGF.sum_of_iIndepFun`,
`tail_max_le`, `projPerp_apply_norm_le`, `norm_gramInv_mulVec_le`, and Theorem 7.21.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.HighDimensionalStatistics
open StatLean.ConcentrationInequalities

variable {n d : ℕ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Corollary 7.22** (Wainwright §7.5): Lasso support recovery under i.i.d. sub-Gaussian
noise. With the regularization choice (7.46), with probability at least `1 − 4e^{−nδ²/2}` the
Lasso solution has support contained in `S` and satisfies the ℓ∞ error bound (7.47).

The noise components `w i : Ω → ℝ` assemble into the response `Y ω = X θ* + w(ω)`. The
conclusion is the high-probability event {no false inclusion ∧ ℓ∞ bound}; uniqueness (7.21a)
also holds on this event via `lasso_support_recovery_unique`. -/
theorem lasso_support_recovery_subgaussian
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : EuclideanSpace ℝ (Fin d))
    (S : Finset (Fin d))
    (w : Fin n → Ω → ℝ)
    (σ2 : ℝ≥0)
    (μ : Measure Ω)
    (lam α cmin C δ : ℝ)
    (βhat : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5
    (hn : 0 < n)
    -- USER-INPUT: 0 < |S| (nonempty support, for log s); Wainwright §7.5
    (hs : 0 < S.card)
    -- USER-INPUT: |S| < d (for log(d − s)); Wainwright §7.5
    (hsd : S.card < d)
    -- USER-INPUT: θ* supported on S; Wainwright §7.5 (S-sparse model)
    (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    -- USER-INPUT: lower-eigenvalue condition (A3); Wainwright §7.5.1 (7.43a)
    (hA3 : LowerEigenvalue X S cmin)
    -- USER-INPUT: 0 < cmin; Wainwright §7.5.1 (7.43a)
    (hcmin : 0 < cmin)
    -- USER-INPUT: mutual incoherence (A4); Wainwright §7.5.1 (7.43b)
    (hA4 : MutualIncoherence X S α)
    -- USER-INPUT: 0 ≤ α; Wainwright §7.5.1
    (hα0 : 0 ≤ α)
    -- USER-INPUT: α < 1; Wainwright §7.5.1
    (hα1 : α < 1)
    -- USER-INPUT: C-column-normalization; Wainwright Cor 7.22
    (hcol : ColumnNormalized X C)
    -- USER-INPUT: noise components jointly independent; Wainwright Cor 7.22
    (hw_indep : iIndepFun w μ)
    -- USER-INPUT: each noise component sub-Gaussian with variance proxy σ²; Wainwright Cor 7.22
    (hw_sg : ∀ i, IsSubGaussian (w i) σ2 μ)
    -- USER-INPUT: each noise component centered; Wainwright Cor 7.22
    (hw_zero : ∀ i, ∫ ω, w i ω ∂μ = 0)
    -- USER-INPUT: 0 < δ; Wainwright Cor 7.22 (7.46)
    (hδ : 0 < δ)
    -- LEAN-ONLY: 0 < σ²; the σ² = 0 case (noise a.s. 0) holds by a separate trivial path
    (hσ2 : 0 < (σ2 : ℝ))
    -- USER-INPUT: regularization choice λₙ = (2Cσ/(1−α))(√(2log(d−s)/n) + δ); Wainwright (7.46)
    (hlam : lam = (2 * C * Real.sqrt σ2 / (1 - α)) *
      (Real.sqrt (2 * Real.log ((d : ℝ) - S.card) / n) + δ))
    -- USER-INPUT: β̂ ω minimises the Lasso for response Y ω = X θ* + w(ω); Wainwright Cor 7.22
    (hLasso : ∀ ω, IsLassoEstimator X
      (designMap X θstar + WithLp.toLp 2 (fun i => w i ω)) lam (βhat ω)) :
    ENNReal.ofReal (1 - 4 * Real.exp (-(n : ℝ) * δ ^ 2 / 2)) ≤
      μ {ω | (∀ j ∉ S, (βhat ω).ofLp j = 0) ∧
        linfNorm (restrict S (βhat ω - θstar)) ≤
          Real.sqrt σ2 / Real.sqrt cmin * (Real.sqrt (2 * Real.log (S.card) / n) + δ)
          + matLinftyNorm (gramInvNorm X S) * lam} := by
  sorry

end StatLean.HighDimensionalStatistics
