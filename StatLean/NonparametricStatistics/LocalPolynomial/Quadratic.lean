import StatLean.NonparametricStatistics.LocalPolynomial.Defs
import StatLean.NonparametricStatistics.Regression.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The local polynomial estimator as a quadratic minimisation

The exact linear algebra of the LP(`ℓ`) criterion: symmetry and positive definiteness of the
local design matrix, the inverse bound from the eigenvalue hypothesis, normal equations,
uniqueness of the minimiser, agreement of the closed-form weights with the minimiser, and
linearity of the estimator.

**Proof formalization notes.** Expanding the square,
`lpObjective θ = ∑ Yᵢ²Kᵢ − 2·(nh)·⟨θ, a_t⟩ + (nh)·⟨θ, B_t θ⟩`; when `B_t ≻ 0` this strictly
convex quadratic has the unique stationary point `B_t θ = a_t`. `lpEstimator` is by
construction `(B_t⁻¹ a_t)₀`, hence equals `θ 0` for any minimiser `θ`. Positive definiteness
follows from the quadratic-form lower bound at positive `lam0` plus symmetry of `B_t` (a sum
of symmetric rank-one blocks `U Uᵀ`). The inverse bound is the Cauchy–Schwarz chain
`lam0·‖w‖² ≤ ⟨w, B w⟩ ≤ ‖w‖·‖B w‖` applied at `w = B⁻¹ v`.

**Bibliographic comments.** V. Ya. Katkovnik, *Soviet Automat. Control* **5** (1979), 25–34;
C. J. Stone, *Ann. Statist.* **5** (1977), 595–620.
-/

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat Y : Fin n → ℝ} {K : ℝ → ℝ} {h : ℝ} {ℓ : ℕ} {t : ℝ}

/-- The local design matrix is symmetric. -/
theorem lpMatrix_isSymm (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ) :
    (lpMatrix xdat K h ℓ t).IsSymm := by
  sorry

/-- A positive uniform quadratic-form lower bound makes the local design matrix positive
definite. -/
theorem lpMatrix_posDef {lam0 : ℝ} (hlam : 0 < lam0)
    (hLB : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k) :
    (lpMatrix xdat K h ℓ t).PosDef := by
  sorry

/-- **Inverse bound from the eigenvalue hypothesis** (squared form):
`‖B_t⁻¹ v‖² ≤ ‖v‖²/lam0²`. -/
theorem lpMatrix_inv_mulVec_sq_le {lam0 : ℝ} (hlam : 0 < lam0)
    (hLB : ∀ v : Fin (ℓ + 1) → ℝ,
      lam0 * ∑ k, (v k) ^ 2 ≤ ∑ k, v k * (lpMatrix xdat K h ℓ t).mulVec v k)
    (v : Fin (ℓ + 1) → ℝ) :
    ∑ k, ((lpMatrix xdat K h ℓ t)⁻¹.mulVec v k) ^ 2
      ≤ (∑ k, (v k) ^ 2) / lam0 ^ 2 := by
  sorry

/-- **Normal equations**: under `B_t ≻ 0`, `θ` minimises the LP(`ℓ`) criterion iff
`B_t θ = a_t`. -/
theorem isLPSolution_iff_normal (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    (θ : Fin (ℓ + 1) → ℝ) :
    IsLPSolution xdat Y K h ℓ t θ
      ↔ (lpMatrix xdat K h ℓ t).mulVec θ = lpRhs xdat Y K h ℓ t := by
  sorry

/-- Existence of the minimiser in closed form: under `B_t ≻ 0`,
`θ̂ = B_t⁻¹ a_t` minimises the LP(`ℓ`) criterion. -/
theorem isLPSolution_inv_mulVec (hpd : (lpMatrix xdat K h ℓ t).PosDef) :
    IsLPSolution xdat Y K h ℓ t
      ((lpMatrix xdat K h ℓ t)⁻¹.mulVec (lpRhs xdat Y K h ℓ t)) := by
  sorry

/-- Uniqueness of the minimiser under `B_t ≻ 0`. -/
theorem isLPSolution_unique (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    {θ₁ θ₂ : Fin (ℓ + 1) → ℝ}
    (h₁ : IsLPSolution xdat Y K h ℓ t θ₁) (h₂ : IsLPSolution xdat Y K h ℓ t θ₂) :
    θ₁ = θ₂ := by
  sorry

/-- **The closed-form estimator is the minimiser's first coordinate**: under `B_t ≻ 0`, for
any minimiser `θ`, `lpEstimator xdat Y K h ℓ t = θ 0` (the classical `f̂(t) = U(0)ᵀθ̂(t)`). -/
theorem lpEstimator_eq_isLPSolution (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    {θ : Fin (ℓ + 1) → ℝ} (hθ : IsLPSolution xdat Y K h ℓ t θ) :
    lpEstimator xdat Y K h ℓ t = θ 0 := by
  sorry

/-- **The LP(`ℓ`) estimator is linear** in the responses: it is given by response-free
weights (immediately from the closed weight form). -/
theorem isLinearEstimator_lpEstimator (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) :
    IsLinearEstimator fun (Y : Fin n → ℝ) (t : ℝ) => lpEstimator xdat Y K h ℓ t := by
  sorry

end StatLean.NonparametricStatistics
