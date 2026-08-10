import StatLean.RobustStatistics.LocationScale.Huber
import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.RobustStatistics.LocationScale.Median

/-!
# Location M-estimates — the finite-sample objective and estimating equation

A location M-estimate for the loss `ρ` is a global minimizer of
`θ ↦ ∑ᵢ ρ(xᵢ - θ)` (`MMY §2.3.1`, eq. (2.13)). This family contains the mean
(`ρ(u) = u²`), the median (`ρ(u) = |u|`) and the Huber estimates, and — for
differentiable `ρ` with score `ψ = ρ'` — is characterized by the estimating equation
`∑ᵢ ψ(xᵢ - θ̂) = 0` (`MMY` eq. (2.19)):

* `IsMLocationEstimate ρ x θ` — `θ` globally minimizes the M-objective.
* `exists_isMLocationEstimate` — existence for continuous coercive losses.
* `IsMLocationEstimate.score_eq_zero` — minimizer ⟹ estimating equation (eq. (2.19)).
* `isMLocationEstimate_of_score_eq_zero` — the converse for convex `ρ`.
* `isMLocationEstimate_comp_add` — the M-estimate correspondence is shift equivariant.
* `isMLocationEstimate_sq_iff` — squared loss ⟺ the sample mean (eq. (2.16)).
* `isMLocationEstimate_abs_sampleMedian` — the median minimizes the L¹ objective
  (eq. (2.18)).
* Huber instances: existence, and the clipped estimating equation.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3.1 (eq.
(2.13), (2.16), (2.18)–(2.19)), Theorem 10.1 (existence/uniqueness of solutions).
-/

open Filter Topology

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- **Location M-estimate** (`MMY §2.3.1`, eq. (2.13)): `θ` is a global minimizer of the
M-objective `t ↦ ∑ᵢ ρ(xᵢ - t)`. For non-convex (redescending) `ρ` this is the absolute
minimum, not a mere estimating-equation root (`MMY §2.4` discussion). -/
def IsMLocationEstimate (ρ : ℝ → ℝ) (x : Fin n → ℝ) (θ : ℝ) : Prop :=
  ∀ t : ℝ, ∑ i, ρ (x i - θ) ≤ ∑ i, ρ (x i - t)

/-- **Existence of location M-estimates** for continuous, bounded-below, coercive losses
(`MMY` Theorem 10.1 context). -/
theorem exists_isMLocationEstimate {ρ : ℝ → ℝ}
    -- USER-INPUT: continuous loss; MMY Thm 10.1 context
    (hρc : Continuous ρ)
    -- USER-INPUT: coercive loss (ρ → ∞ as |u| → ∞); MMY §2.3.1 (ρ-function, R3)
    (hρ_coer : Tendsto ρ (cocompact ℝ) atTop)
    -- LEAN-ONLY: bounded below, so that one escaping term cannot be cancelled; free for
    -- ρ-functions, which are nonnegative (MMY Def 2.1 R1–R2)
    (hρ_bdd : BddBelow (Set.range ρ))
    (x : Fin n → ℝ) :
    ∃ θ : ℝ, IsMLocationEstimate ρ x θ := by
  sorry

/-- **The estimating equation** (`MMY §2.3.1`, eq. (2.19)): at an M-estimate for a
differentiable loss, the score sum vanishes, `∑ᵢ ψ(xᵢ - θ̂) = 0`. -/
theorem IsMLocationEstimate.score_eq_zero {ρ ψ : ℝ → ℝ} {x : Fin n → ℝ} {θ : ℝ}
    -- USER-INPUT: differentiable loss with score ψ = ρ'; MMY eq. (2.19)
    (hρ : ∀ u, HasDerivAt ρ (ψ u) u)
    (hθ : IsMLocationEstimate ρ x θ) :
    ∑ i, ψ (x i - θ) = 0 := by
  sorry

/-- **The convex converse** (`MMY §2.4`, eq. (2.40) discussion): for convex differentiable
`ρ`, any root of the estimating equation is a global M-estimate. -/
theorem isMLocationEstimate_of_score_eq_zero {ρ ψ : ℝ → ℝ} {x : Fin n → ℝ} {θ : ℝ}
    -- USER-INPUT: convex loss; MMY §2.4 eq. (2.40)
    (hρ_conv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: differentiable loss with score ψ = ρ'; MMY eq. (2.19)
    (hρ : ∀ u, HasDerivAt ρ (ψ u) u)
    (hscore : ∑ i, ψ (x i - θ) = 0) :
    IsMLocationEstimate ρ x θ := by
  sorry

/-- **Shift equivariance of the M-estimate correspondence** (`MMY §2.3.1`, Problem 2.5):
`θ + a` is an M-estimate for the shifted sample `x + a·𝟙` iff `θ` is one for `x`. -/
theorem isMLocationEstimate_comp_add {ρ : ℝ → ℝ} {x : Fin n → ℝ} {θ a : ℝ} :
    IsMLocationEstimate ρ (x + a • (1 : Fin n → ℝ)) (θ + a) ↔ IsMLocationEstimate ρ x θ := by
  sorry

/-- **Squared loss recovers the sample mean** (`MMY §2.3.1`, eq. (2.16)): for `n ≥ 1`,
`θ` minimizes `∑ (xᵢ - θ)²` iff `θ = x̄`. -/
theorem isMLocationEstimate_sq_iff {x : Fin n → ℝ} {θ : ℝ} (hn : 0 < n) :
    IsMLocationEstimate (fun u => u ^ 2) x θ ↔ θ = sampleMean x := by
  sorry

/-- **The median minimizes the L¹ objective** (`MMY §2.3.1`, eq. (2.18), (2.21)): the
sample median is an M-estimate for the absolute-value loss. (For even `n` the low median
is one of the minimizers.) -/
theorem isMLocationEstimate_abs_sampleMedian (x : Fin n → ℝ) :
    IsMLocationEstimate (fun u => |u|) x (sampleMedian x) := by
  sorry

/-! ### Huber location estimates (`MMY §2.3.2`) -/

/-- Huber location estimates exist for every sample. -/
theorem exists_isMLocationEstimate_huber {c : ℝ} (hc : 0 < c) (x : Fin n → ℝ) :
    ∃ θ : ℝ, IsMLocationEstimate (huberRho c) x θ := by
  sorry

/-- **The Huber estimating equation** (`MMY` eq. (2.19) with eq. (2.29)): at a Huber
M-estimate, the clipped residuals sum to zero. -/
theorem IsMLocationEstimate.huber_score_eq_zero {c : ℝ} (hc : 0 ≤ c) {x : Fin n → ℝ}
    {θ : ℝ} (hθ : IsMLocationEstimate (huberRho c) x θ) :
    ∑ i, huberPsi c (x i - θ) = 0 := by
  sorry

/-- **A Huber score root is a Huber M-estimate** (convexity of `ρ_c`). -/
theorem isMLocationEstimate_huber_of_score_eq_zero {c : ℝ} (hc : 0 ≤ c) {x : Fin n → ℝ}
    {θ : ℝ} (hscore : ∑ i, huberPsi c (x i - θ) = 0) :
    IsMLocationEstimate (huberRho c) x θ := by
  sorry

end StatLean.RobustStatistics
