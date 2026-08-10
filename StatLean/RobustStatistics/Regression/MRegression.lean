import StatLean.RobustStatistics.LocationScale.Huber
import Mathlib.Analysis.Convex.Function

/-!
# Regression M-estimates — objective, normal equations, and the leverage problem

A regression M-estimate for the loss `ρ` (known scale, absorbed into `ρ`) minimizes
`β ↦ ∑ᵢ ρ(yᵢ - xᵢᵀβ)` (`MMY §4.4`, eq. (4.36)/(4.39)); for differentiable `ρ` with score
`ψ = ρ'` it satisfies the M-analogue of the normal equations
`∑ᵢ ψ(yᵢ - xᵢᵀβ̂)·xᵢ = 0` (`MMY` eq. (4.37)/(4.40)).

* `IsMRegressionEstimate` — global minimizer of the M-objective.
* `IsMRegressionEstimate.normalEquation` — the estimating equation (4.40).
* `quadraticMRegression_normalEquation` — squared loss recovers the OLS normal equations.
* `huberRegression_convex` — the Huber regression objective is convex in `β`.
* `isMRegressionEstimate_regressionEquivariant` — regression equivariance (`MMY` (4.48)).
* `huberRegression_score_leverage_unbounded` — **the leverage counterexample**: the
  estimating-equation contribution `x·ψ(y - xβ)` of a single observation is unbounded in
  the design point `x` even for the bounded Huber score. A bounded residual score alone
  does not give bounded influence in regression — the design factor survives — which is
  what motivates GM- and high-breakdown regression estimators (`MMY §5`).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §4.4 (eq.
(4.36)–(4.40)), §4.4.2 (eq. (4.48)), §5.11 (GM-estimators motivation).
-/

open Finset

namespace StatLean.RobustStatistics

variable {n p : ℕ}

/-- **Regression M-estimate** (`MMY §4.4`, eq. (4.39) with known scale): `β` globally
minimizes the M-objective `b ↦ ∑ᵢ ρ(yᵢ - ∑ⱼ Xᵢⱼ bⱼ)`. -/
def IsMRegressionEstimate (ρ : ℝ → ℝ) (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : Prop :=
  ∀ b : Fin p → ℝ, ∑ i, ρ (y i - ∑ j, X i j * β j) ≤ ∑ i, ρ (y i - ∑ j, X i j * b j)

/-- **The M-normal equations** (`MMY` eq. (4.40)): at a regression M-estimate for a
differentiable loss, the score-weighted design columns sum to zero. -/
theorem IsMRegressionEstimate.normalEquation {ρ ψ : ℝ → ℝ} {X : Fin n → Fin p → ℝ}
    {y : Fin n → ℝ} {β : Fin p → ℝ}
    -- USER-INPUT: differentiable loss with score ψ = ρ'; MMY eq. (4.40)
    (hρ : ∀ u, HasDerivAt ρ (ψ u) u)
    (hβ : IsMRegressionEstimate ρ X y β) (j : Fin p) :
    ∑ i, ψ (y i - ∑ k, X i k * β k) * X i j = 0 := by
  sorry

/-- **Squared loss recovers the least-squares normal equations** (`MMY` eq. (4.37) with
`ψ₀(u) = u`, i.e. `ρ(u) = u²/2`). -/
theorem quadraticMRegression_normalEquation {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ}
    {β : Fin p → ℝ}
    (hβ : IsMRegressionEstimate (fun u => u ^ 2 / 2) X y β) (j : Fin p) :
    ∑ i, (y i - ∑ k, X i k * β k) * X i j = 0 := by
  sorry

/-- **Convexity of M-regression objectives for convex losses** (`MMY §4.4`): the
composition with the affine residual map preserves convexity in `β`; in particular the
Huber regression objective is convex. -/
theorem mRegression_objective_convex {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss; MMY §4.4 (monotone M-estimators come from convex ρ)
    (hρ : ConvexOn ℝ Set.univ ρ) (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun b : Fin p → ℝ => ∑ i, ρ (y i - ∑ j, X i j * b j)) := by
  sorry

/-- The Huber regression objective is convex in `β` (`MMY §4.4`). -/
theorem huberRegression_convex {c : ℝ} (hc : 0 ≤ c) (X : Fin n → Fin p → ℝ)
    (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun b : Fin p → ℝ => ∑ i, huberRho c (y i - ∑ j, X i j * b j)) := by
  sorry

/-- **Regression equivariance of the M-estimate correspondence** (`MMY` eq. (4.48)):
adding `Xγ` to the responses shifts the M-estimates by `γ`. -/
theorem isMRegressionEstimate_regressionEquivariant {ρ : ℝ → ℝ} {X : Fin n → Fin p → ℝ}
    {y : Fin n → ℝ} {β γ : Fin p → ℝ} :
    IsMRegressionEstimate ρ X (fun i => y i + ∑ j, X i j * γ j) (β + γ) ↔
      IsMRegressionEstimate ρ X y β := by
  sorry

/-- **The leverage counterexample** (`MMY §4.4` discussion, §5.11 motivation): the
single-observation contribution `x·ψ_c(y - xβ)` to the Huber estimating equation is
unbounded in the design point — for any bound `B` there is a design/response pair whose
contribution exceeds `B`, even though `|ψ_c| ≤ c`. Bounded residual score does **not**
give bounded influence in regression; the design factor `x` survives. -/
theorem huberRegression_score_leverage_unbounded {c : ℝ} (hc : 0 < c) (β : ℝ) :
    ∀ B : ℝ, ∃ x₀ y₀ : ℝ, B < |x₀ * huberPsi c (y₀ - x₀ * β)| := by
  sorry

end StatLean.RobustStatistics
