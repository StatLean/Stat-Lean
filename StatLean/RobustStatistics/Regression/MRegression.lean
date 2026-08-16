import StatLean.RobustStatistics.LocationScale.Huber
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Pow

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
  -- The design column `j` is picked out by the coordinate direction `Pi.single j 1`.
  have hcol : ∀ (t : ℝ) (i : Fin n),
      ∑ k, X i k * (β + t • (Pi.single j 1 : Fin p → ℝ)) k
        = (∑ k, X i k * β k) + t * X i j := by
    intro t i
    have h1 : ∀ k : Fin p, X i k * (β + t • (Pi.single j 1 : Fin p → ℝ)) k
        = X i k * β k + t * (X i k * (Pi.single j 1 : Fin p → ℝ) k) := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : ∑ k, X i k * (Pi.single j 1 : Fin p → ℝ) k = X i j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h3 : ∑ k, X i k * (β + t • (Pi.single j 1 : Fin p → ℝ)) k
        = ∑ k, (X i k * β k + t * (X i k * (Pi.single j 1 : Fin p → ℝ) k)) :=
      Finset.sum_congr rfl fun k _ => h1 k
    rw [h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2]
  -- The restriction of the objective to the line through `β` in the direction `j`
  -- has a global minimum at `t = 0`.
  have hline : ∀ t : ℝ,
      ∑ i, ρ (y i - ∑ k, X i k * β k)
        ≤ ∑ i, ρ ((y i - ∑ k, X i k * β k) - t * X i j) := by
    intro t
    refine le_trans (hβ (β + t • (Pi.single j 1 : Fin p → ℝ)))
      (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [hcol t i]
    congr 1
    ring
  have hmin : IsLocalMin
      (fun s : ℝ => ∑ i, ρ ((y i - ∑ k, X i k * β k) - s * X i j)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simpa using hline t
  have hderiv : HasDerivAt
      (fun s : ℝ => ∑ i, ρ ((y i - ∑ k, X i k * β k) - s * X i j))
      (∑ i, ψ (y i - ∑ k, X i k * β k) * -X i j) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hin : HasDerivAt (fun s : ℝ => (y i - ∑ k, X i k * β k) - s * X i j) (-X i j) 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℝ)).mul_const (X i j)).const_sub (y i - ∑ k, X i k * β k)
    have hout : HasDerivAt ρ (ψ (y i - ∑ k, X i k * β k))
        ((fun s : ℝ => (y i - ∑ k, X i k * β k) - s * X i j) 0) := by
      simpa using hρ (y i - ∑ k, X i k * β k)
    exact hout.comp 0 hin
  simpa using hmin.hasDerivAt_eq_zero hderiv

/-- **Squared loss recovers the least-squares normal equations** (`MMY` eq. (4.37) with
`ψ₀(u) = u`, i.e. `ρ(u) = u²/2`). -/
theorem quadraticMRegression_normalEquation {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ}
    {β : Fin p → ℝ}
    (hβ : IsMRegressionEstimate (fun u => u ^ 2 / 2) X y β) (j : Fin p) :
    ∑ i, (y i - ∑ k, X i k * β k) * X i j = 0 := by
  have hρ : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v ^ 2 / 2) u u := by
    intro u
    simpa using (hasDerivAt_pow 2 u).div_const 2
  exact hβ.normalEquation hρ j

/-- **Convexity of M-regression objectives for convex losses** (`MMY §4.4`): the
composition with the affine residual map preserves convexity in `β`; in particular the
Huber regression objective is convex. -/
theorem mRegression_objective_convex {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss; MMY §4.4 (monotone M-estimators come from convex ρ)
    (hρ : ConvexOn ℝ Set.univ ρ) (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun b : Fin p → ℝ => ∑ i, ρ (y i - ∑ j, X i j * b j)) := by
  refine ⟨convex_univ, fun b₁ _ b₂ _ a c ha hc hac => ?_⟩
  -- the residual is affine in `b`, and `a + c = 1` also splits the response term
  have key : ∀ i : Fin n,
      y i - ∑ j, X i j * (a • b₁ + c • b₂) j
        = a * (y i - ∑ j, X i j * b₁ j) + c * (y i - ∑ j, X i j * b₂ j) := by
    intro i
    have h1 : ∑ j, X i j * (a • b₁ + c • b₂) j
        = a * (∑ j, X i j * b₁ j) + c * (∑ j, X i j * b₂ j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1]
    linear_combination (-(y i)) * hac
  simp only [smul_eq_mul]
  calc ∑ i, ρ (y i - ∑ j, X i j * (a • b₁ + c • b₂) j)
      = ∑ i, ρ (a * (y i - ∑ j, X i j * b₁ j) + c * (y i - ∑ j, X i j * b₂ j)) :=
        Finset.sum_congr rfl fun i _ => by rw [key i]
    _ ≤ ∑ i, (a * ρ (y i - ∑ j, X i j * b₁ j) + c * ρ (y i - ∑ j, X i j * b₂ j)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [smul_eq_mul] using
          hρ.2 (Set.mem_univ (y i - ∑ j, X i j * b₁ j))
            (Set.mem_univ (y i - ∑ j, X i j * b₂ j)) ha hc hac
    _ = a * (∑ i, ρ (y i - ∑ j, X i j * b₁ j)) + c * ∑ i, ρ (y i - ∑ j, X i j * b₂ j) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The Huber regression objective is convex in `β` (`MMY §4.4`). -/
theorem huberRegression_convex {c : ℝ} (hc : 0 ≤ c) (X : Fin n → Fin p → ℝ)
    (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (fun b : Fin p → ℝ => ∑ i, huberRho c (y i - ∑ j, X i j * b j)) :=
  mRegression_objective_convex (huberRho_convex hc) X y

/-- **Regression equivariance of the M-estimate correspondence** (`MMY` eq. (4.48)):
adding `Xγ` to the responses shifts the M-estimates by `γ`. -/
theorem isMRegressionEstimate_regressionEquivariant {ρ : ℝ → ℝ} {X : Fin n → Fin p → ℝ}
    {y : Fin n → ℝ} {β γ : Fin p → ℝ} :
    IsMRegressionEstimate ρ X (fun i => y i + ∑ j, X i j * γ j) (β + γ) ↔
      IsMRegressionEstimate ρ X y β := by
  -- shifting the responses by `Xγ` and the parameter by `γ` leaves the residuals unchanged
  have key : ∀ (b : Fin p → ℝ) (i : Fin n),
      (y i + ∑ j, X i j * γ j) - ∑ j, X i j * (b + γ) j = y i - ∑ j, X i j * b j := by
    intro b i
    have h1 : ∑ j, X i j * (b + γ) j = (∑ j, X i j * b j) + ∑ j, X i j * γ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply]
      ring
    rw [h1]
    ring
  constructor
  · intro h b
    simpa only [key] using h (b + γ)
  · intro h b
    have hbg : b - γ + γ = b := by abel
    calc ∑ i, ρ ((y i + ∑ j, X i j * γ j) - ∑ j, X i j * (β + γ) j)
        = ∑ i, ρ (y i - ∑ j, X i j * β j) := by simp only [key]
      _ ≤ ∑ i, ρ (y i - ∑ j, X i j * (b - γ) j) := h (b - γ)
      _ = ∑ i, ρ ((y i + ∑ j, X i j * γ j) - ∑ j, X i j * ((b - γ) + γ) j) := by
          simp only [key]
      _ = ∑ i, ρ ((y i + ∑ j, X i j * γ j) - ∑ j, X i j * b j) := by rw [hbg]

/-- **The leverage counterexample** (`MMY §4.4` discussion, §5.11 motivation): the
single-observation contribution `x·ψ_c(y - xβ)` to the Huber estimating equation is
unbounded in the design point — for any bound `B` there is a design/response pair whose
contribution exceeds `B`, even though `|ψ_c| ≤ c`. Bounded residual score does **not**
give bounded influence in regression; the design factor `x` survives. -/
theorem huberRegression_score_leverage_unbounded {c : ℝ} (hc : 0 < c) (β : ℝ) :
    ∀ B : ℝ, ∃ x₀ y₀ : ℝ, B < |x₀ * huberPsi c (y₀ - x₀ * β)| := by
  intro B
  have hcne : c ≠ 0 := ne_of_gt hc
  -- put the residual right at the clipping threshold `c`, and take the leverage large
  refine ⟨max B 0 / c + 1, (max B 0 / c + 1) * β + c, ?_⟩
  have hres : (max B 0 / c + 1) * β + c - (max B 0 / c + 1) * β = c := by ring
  rw [hres, huberPsi_of_abs_le hc.le (le_of_eq (abs_of_pos hc))]
  have hdiv : 0 ≤ max B 0 / c := div_nonneg (le_max_right B 0) hc.le
  have hx0 : 0 < max B 0 / c + 1 := by linarith
  rw [abs_of_pos (mul_pos hx0 hc)]
  have heq : (max B 0 / c + 1) * c = max B 0 + c := by field_simp
  rw [heq]
  linarith [le_max_left B 0]

end StatLean.RobustStatistics
