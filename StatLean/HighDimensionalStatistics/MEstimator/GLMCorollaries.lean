import StatLean.HighDimensionalStatistics.MEstimator.GoodEvent
import StatLean.HighDimensionalStatistics.MEstimator.L1Decomposable
import StatLean.HighDimensionalStatistics.MEstimator.Bound
import StatLean.HighDimensionalStatistics.MEstimator.DualBound

/-!
# GLM Lasso estimation-error rates (Wainwright Corollaries 9.26, 9.27)

The payoff of the chapter for sparse generalized linear models. Combining the deterministic bounds
(Corollary 9.20 for `ℓ₂`/`ℓ₁`, Theorem 9.24 for `ℓ∞`) — instantiated at the `ℓ₁/ℓ∞` decomposable
regularizer `l1DecomposableReg S` with `Ψ(M(S)) = √s` — with the high-probability good event
(`good_event_highProb`), the `ℓ₁`-regularized GLM Lasso `θ̂` satisfies, with probability
`≥ 1 − 2e^{−2nδ²}`:
* `‖θ̂ − θ*‖₂² ≲ s·λ²/κ²` and `‖θ̂ − θ*‖₁ ≲ s·λ/κ` (Corollary 9.26), and
* `‖θ̂ − θ*‖∞ ≤ 3λ/κ` under an additional `ℓ∞`-curvature condition (Corollary 9.27),
with `λ = 4BC{√(log d/n) + δ}`.

The RSC condition (9.62) and the `ℓ∞`-curvature condition (9.64) are `USER-INPUT` — the book
establishes them separately (Theorem 9.36, for sub-Gaussian covariates), out of scope here.

Constant note: the deterministic `ℓ₂`/`ℓ₁` constants are the provable `144`/`48` (see `Bound.lean`),
vs. the book's `9/4`/`6`; same `s·λ²/κ²` rate.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The GLM cost `glmCost M ω` is convex (its Hessian is `(1/n)∑ᵢ ψ''(⟨xᵢ,θ⟩) xᵢxᵢᵀ ⪰ 0` since
`ψ'' ≥ 0`). -/
theorem glmCost_convexOn (M : GLMExpFamily n d μ) (ω : Ω) :
    ConvexOn ℝ Set.univ (glmCost M ω) := by
  sorry

/-- The GLM cost `glmCost M ω` is differentiable. -/
theorem glmCost_differentiable (M : GLMExpFamily n d μ) (ω : Ω) :
    Differentiable ℝ (glmCost M ω) := by
  sorry

/-- **The score is the gradient of the GLM cost at `θ*`.** `∇(glmCost M ω)(θ*) = scoreVec M ω`,
i.e. `(1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢ`. (Chain rule on each `ψ(⟨xᵢ,·⟩)` + linearity of `gradient`.) -/
theorem glmCost_gradient_eq_scoreVec (M : GLMExpFamily n d μ) (ω : Ω) :
    gradient (glmCost M ω) M.θstar = scoreVec M ω := by
  sorry

/-- **Subspace Lipschitz constant of `ℓ₁` over `M(S)` is `√s`** (Wainwright §9.4, p.279):
`Ψ(M(S)) = sup_{u∈M(S), ‖u‖₂≤1} ‖u‖₁ = √|S|`. From `l1Norm_restrict_le_sqrt_card_mul_norm`. -/
theorem subspaceLip_l1_suppSubmodule (S : Finset (Fin d)) :
    subspaceLip (l1Seminorm d) (suppSubmodule S) = Real.sqrt S.card := by
  sorry

/-- **Corollary 9.26 — GLM Lasso `ℓ₂`/`ℓ₁` rates.** Under (G1) column normalization, (G2) the GLM
exp-family with `0 ≤ ψ'' ≤ B²`, the RSC condition (9.62) at `θ*` (USER-INPUT), `θ*` supported on `S`
(`s = |S|`), and `λ = 4BC{√(log d/n) + δ}`, the `ℓ₁`-regularized GLM Lasso satisfies, with probability
`≥ 1 − 2e^{−2nδ²}`,
`‖θ̂ − θ*‖₂² ≤ 144·s·λ²/κ²` and `‖θ̂ − θ*‖₁ ≤ 48·s·λ/κ`. -/
theorem glm_lasso_l2_l1_rate (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (S : Finset (Fin d)) (C κ R δ lam : ℝ) (θhat : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: (G1) column normalization; Wainwright §9.5.
    (hC : IsColumnNormalized M.X C)
    (hn : 0 < n) (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hB : 0 < M.B) (hCpos : 0 < C)
    -- USER-INPUT: target is `s`-sparse, supported on `S`; Wainwright Cor 9.26.
    (hsparse : M.θstar ∈ suppSubmodule S)
    -- USER-INPUT: RSC condition (9.62) for the GLM cost (radius `1`, tolerance `c₁ log d/n`); Wainwright Cor 9.26 (defers to Thm 9.36).
    (τSq : ℝ) (hτSq : 0 ≤ τSq)
    (hRSC : ∀ ω, RSC (glmCost M ω) M.θstar (l1Seminorm d) κ R τSq)
    -- USER-INPUT: slack `τ²·s ≤ κ/128`; Wainwright Cor 9.26 (sample-size condition).
    (hslack : τSq * (S.card : ℝ) ≤ κ / 128)
    -- USER-INPUT: `εₙ² ≤ R²` localization; Wainwright Cor 9.26.
    (hεR : 144 * (lam ^ 2 / κ ^ 2) * (S.card : ℝ) ≤ R ^ 2)
    -- USER-INPUT: tuning `λ = 4BC{√(log d/n) + δ}`; Wainwright Cor 9.26.
    (hlam : lam = 4 * M.B * C * (Real.sqrt (Real.log d / n) + δ))
    -- USER-INPUT: `θ̂ ω` minimizes the GLM Lasso objective `glmCost + λ‖·‖₁`; Wainwright eq 9.61.
    (hopt : ∀ ω θ, glmCost M ω (θhat ω) + lam * l1Norm (θhat ω)
        ≤ glmCost M ω θ + lam * l1Norm θ) :
    ENNReal.ofReal (1 - 2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)) ≤
      μ {ω | ‖θhat ω - M.θstar‖ ^ 2 ≤ 144 * (lam ^ 2 / κ ^ 2) * (S.card : ℝ)
          ∧ l1Norm (θhat ω - M.θstar) ≤ 48 * (lam / κ) * (S.card : ℝ)} := by
  sorry

/-- **Corollary 9.27 — GLM Lasso `ℓ∞` rate.** In addition to the Corollary 9.26 hypotheses, under the
`ℓ∞`-curvature condition (9.64) (USER-INPUT) and the localization `Φ*(θ̂−θ*) ≤ R`, the GLM Lasso
satisfies `‖θ̂ − θ*‖∞ ≤ 3λ/κ` with probability `≥ 1 − 2e^{−2nδ²}`. -/
theorem glm_lasso_linf_rate (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (S : Finset (Fin d)) (C κ τ R δ lam : ℝ) (θhat : Ω → EuclideanSpace ℝ (Fin d))
    (hC : IsColumnNormalized M.X C)
    (hn : 0 < n) (hd : 0 < d) (hκ : 0 < κ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hB : 0 < M.B) (hCpos : 0 < C)
    (hsparse : M.θstar ∈ suppSubmodule S)
    -- USER-INPUT: `ℓ∞`-curvature condition (9.64) for the GLM cost; Wainwright Cor 9.27.
    (hcurv : ∀ ω, dualCurvature (glmCost M ω) M.θstar (l1Seminorm d) (linfSeminorm d) κ τ R)
    -- USER-INPUT: slack `τ·s < κ/32`; Wainwright Cor 9.27.
    (hslack : τ * (S.card : ℝ) < κ / 32)
    -- USER-INPUT: localization `Φ*(θ̂−θ*) ≤ R`; Wainwright Cor 9.27.
    (hRloc : ∀ ω, linfNorm (θhat ω - M.θstar) ≤ R)
    -- USER-INPUT: tuning; Wainwright Cor 9.27.
    (hlam : lam = 2 * M.B * C * (Real.sqrt (Real.log d / n) + δ))
    (hopt : ∀ ω θ, glmCost M ω (θhat ω) + lam * l1Norm (θhat ω)
        ≤ glmCost M ω θ + lam * l1Norm θ) :
    ENNReal.ofReal (1 - 2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)) ≤
      μ {ω | linfNorm (θhat ω - M.θstar) ≤ 3 * lam / κ} := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
