import StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gram matrix `XₛᵀXₛ`, its inverse, and the projection `Π_{S⊥}` (ForMathlib)

Theorem-agnostic matrix analysis for Lasso support recovery (Wainwright §7.5):
the support Gram matrix `XₛᵀXₛ`, its inverse `(XₛᵀXₛ)⁻¹`, and the orthogonal
projection `Π_{S⊥}(X) = Iₙ − Xₛ(XₛᵀXₛ)⁻¹Xₛᵀ`.

Book-agnostic: positive-definiteness/invertibility and the operator bounds take the
**quadratic-form coercivity** `cmin·‖v‖² ≤ (1/n)·‖Xₛ v‖²` as a *plain hypothesis*
(this is condition (A3) unfolded; the concept-layer `LowerEigenvalue` supplies it, but
naming it here would invert the `ForMathlib → concept` dependency). All inputs are
hypothesis-free identities or this coercivity adapter; tagged `-- LEAN-ONLY` accordingly.

Mathlib bricks: `Matrix.PosDef`, `Matrix.PosDef.isUnit_det` / `Matrix.nonsing_inv`,
min-eigenvalue quadratic-form bound. The matrix ℓ∞ operator norm is given locally as
`matLinftyNorm A = ⨆ i, ∑ j |A i j|` (max absolute row sum = Mathlib `Matrix.linfty_opNorm`).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Support Gram matrix** `G_S = XₛᵀXₛ : Matrix ↥S ↥S ℝ`. -/
def gram (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix {x // x ∈ S} {x // x ∈ S} ℝ :=
  (Xsub X S)ᵀ * (Xsub X S)

/-- **Inverse support Gram** `(XₛᵀXₛ)⁻¹`. Equal to the genuine two-sided inverse once
the Gram is invertible (`gram_isUnit_det`), and to the junk `0` otherwise (Mathlib
`Matrix.inv` convention). -/
noncomputable def gramInv (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix {x // x ∈ S} {x // x ∈ S} ℝ :=
  (gram X S)⁻¹

/-- **Orthogonal projection** onto the complement of `colspan(Xₛ)`:
`Π_{S⊥}(X) = Iₙ − Xₛ (XₛᵀXₛ)⁻¹ Xₛᵀ`. -/
noncomputable def projPerp (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - (Xsub X S) * (gramInv X S) * (Xsub X S)ᵀ

/-- **Matrix ℓ∞ operator norm** `|||A|||_∞ = max_i ∑_j |A i j|` (max absolute row sum);
the matrix norm appearing in Wainwright's bound (7.45). Equals Mathlib's
`Matrix.linfty_opNorm`. For an empty row index it is `0`. -/
noncomputable def matLinftyNorm {p q : Type*} [Fintype q]
    (A : Matrix p q ℝ) : ℝ :=
  ⨆ i, ∑ j, |A i j|

/-- Gram quadratic form: `vᵀ G_S v = ‖Xₛ v‖²`. -/
lemma gram_quadForm (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (v : EuclideanSpace ℝ {x // x ∈ S}) :
    (gram X S).mulVec v.ofLp ⬝ᵥ v.ofLp = ‖designSub X S v‖ ^ 2 := by
  sorry

/-- The Gram matrix is symmetric (Hermitian over ℝ). -/
lemma gram_isHermitian (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (gram X S).IsHermitian := by
  sorry

/-- **(A3) ⇒ positive definiteness.** The quadratic-form coercivity makes `G_S` PosDef. -/
lemma gram_posDef_of_coercive (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ}
    -- LEAN-ONLY: 0 < n (needed to clear the 1/n in the Rayleigh quotient)
    (hn : 0 < n)
    -- LEAN-ONLY: 0 < cmin; Wainwright §7.5 (A3, 7.43a)
    (hcmin : 0 < cmin)
    -- LEAN-ONLY: quadratic-form coercivity = (A3) unfolded; supplied by `LowerEigenvalue`
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (gram X S).PosDef := by
  sorry

/-- **(A3) ⇒ invertibility.** The Gram determinant is a unit, so `gramInv` is the genuine
two-sided inverse. -/
lemma gram_isUnit_det (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    IsUnit (gram X S).det := by
  sorry

/-- `gramInv` is a left inverse of `gram` (on vectors), under (A3). -/
lemma gramInv_mulVec_gram (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : {x // x ∈ S} → ℝ) :
    (gramInv X S).mulVec ((gram X S).mulVec u) = u := by
  sorry

/-- `gramInv` is symmetric (inverse of a Hermitian matrix is Hermitian). -/
lemma gramInv_isHermitian (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (gramInv X S).IsHermitian := by
  sorry

/-- **Operator-ℓ² bound on the inverse Gram** from the min-eigenvalue (A3):
`‖(XₛᵀXₛ)⁻¹ u‖ ≤ (1/(cmin·n))·‖u‖`. (Equivalently `‖(XₛᵀXₛ/n)⁻¹‖₂ ≤ 1/cmin`.) -/
lemma norm_gramInv_mulVec_le (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : EuclideanSpace ℝ {x // x ∈ S}) :
    ‖(WithLp.toLp 2 ((gramInv X S).mulVec u.ofLp) : EuclideanSpace ℝ {x // x ∈ S})‖
      ≤ (1 / (cmin * n)) * ‖u‖ := by
  sorry

/-- **The projection is contractive**: `‖Π_{S⊥}(X) u‖ ≤ ‖u‖`. -/
lemma projPerp_apply_norm_le (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 ((projPerp X S).mulVec u.ofLp) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖u‖ := by
  sorry

/-- The projection is idempotent: `Π_{S⊥}(X)² = Π_{S⊥}(X)`. -/
lemma projPerp_idempotent (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (projPerp X S) * (projPerp X S) = projPerp X S := by
  sorry

/-- **Matrix ℓ∞ operator bound** `‖A v‖_∞ ≤ |||A|||_∞ · ‖v‖_∞` (coordinatewise form). -/
lemma matLinftyNorm_mulVec_le {p q : Type*} [Finite p] [Fintype q] [Nonempty p]
    (A : Matrix p q ℝ) (v : q → ℝ) :
    (⨆ i, |(A.mulVec v) i|) ≤ matLinftyNorm A * (⨆ j, |v j|) := by
  sorry

end StatLean.HighDimensionalStatistics
