import StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
import StatLean.HighDimensionalStatistics.ForMathlib.GramMatrix
import StatLean.HighDimensionalStatistics.Lasso.Defs

/-!
# Lasso support recovery — definitions (Wainwright §7.5)

Concept-layer (laptop-only) book-facing predicates for variable-selection consistency
of the Lagrangian Lasso (Wainwright, *High-Dimensional Statistics*, §7.5.1):

* `LowerEigenvalue X S cmin` — condition **(A3)** (7.43a), the lower-eigenvalue bound,
  in quadratic-form (Rayleigh-quotient) form: `γ_min(XₛᵀXₛ/n) ≥ cmin`.
* `MutualIncoherence X S α`  — condition **(A4)** (7.43b), the mutual-incoherence bound.
* `IsL1Subgradient z θ`      — `z ∈ ∂‖θ‖₁` (subdifferential of the ℓ¹ norm, §7.5.2).
* `IsKKT X Y λ θ z`          — the zero-subgradient / KKT condition (7.48).
* `ColumnNormalized X C`     — the C-column-normalization condition of Corollary 7.22.
* `supportRecoveryBound`     — `B(λ;X)` of the ℓ∞ error bound (7.45).

The **Lasso objective itself is reused** from `Lasso/Defs.lean` (`lassoObjective`,
`IsLassoEstimator`) — identical to Wainwright's Lagrangian Lasso (7.18). Reuses
`designSub` / `Xsub` / `col` (`SupportSubmatrix.lean`), `gram` / `gramInv` / `matLinftyNorm`
(`GramMatrix.lean`), and `designMap` / `restrict` (`LinearModel`, `VecNorms`).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Lower-eigenvalue condition (A3)** (Wainwright §7.5.1, 7.43a). Constitutive: the
sample Gram submatrix on the support has smallest eigenvalue `≥ cmin > 0`. Stated in
equivalent **quadratic-form (Rayleigh-quotient)** form `cmin·‖v‖² ≤ (1/n)·‖Xₛ v‖²`
for all `v` on the support; this is `γ_min(XₛᵀXₛ/n) ≥ cmin` by Courant–Fischer. -/
def LowerEigenvalue (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (cmin : ℝ) :
    Prop :=
  ∀ v : EuclideanSpace ℝ {x // x ∈ S},
    cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2

/-- **Mutual-incoherence condition (A4)** (Wainwright §7.5.1, 7.43b). Constitutive:
for every off-support column `X_j` (`j ∉ S`), the regression coefficients of `X_j` on
the support columns have ℓ¹ norm `≤ α`, i.e. `‖(XₛᵀXₛ)⁻¹ Xₛᵀ X_j‖₁ ≤ α`. -/
def MutualIncoherence (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (α : ℝ) :
    Prop :=
  ∀ j ∉ S,
    (∑ i : {x // x ∈ S},
      |((gramInv X S).mulVec ((Xsub X S)ᵀ.mulVec (col X j).ofLp)) i|) ≤ α

/-- **Subdifferential of the ℓ¹ norm** (Wainwright §7.5.2): `z ∈ ∂‖θ‖₁` iff
`z_j = sign(θ_j)` for every `j`, with `sign 0` free in `[-1,1]`. -/
def IsL1Subgradient (z θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i, (0 < θ.ofLp i → z.ofLp i = 1) ∧ (θ.ofLp i < 0 → z.ofLp i = -1) ∧ |z.ofLp i| ≤ 1

/-- **Zero-subgradient / KKT condition** (Wainwright §7.5.2, 7.48):
`(1/n) Xᵀ(X θ − Y) + λ z = 0`, the optimality condition of the Lagrangian Lasso. -/
def IsKKT (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (θ z : EuclideanSpace ℝ (Fin d)) : Prop :=
  (1 / (n : ℝ)) • designMap Xᵀ (designMap X θ - Y) + lam • z = 0

/-- **C-column-normalization condition** (Wainwright Cor 7.22): every design column has
ℓ² norm `≤ C√n`, i.e. `max_j ‖X_j‖₂/√n ≤ C`. -/
def ColumnNormalized (X : Matrix (Fin n) (Fin d) ℝ) (C : ℝ) : Prop :=
  ∀ j, ‖col X j‖ ≤ C * Real.sqrt n

/-- The inverse of the *normalized* Gram `(XₛᵀXₛ/n)⁻¹` appearing in the bound (7.45). -/
noncomputable def gramInvNorm (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix {x // x ∈ S} {x // x ∈ S} ℝ :=
  ((1 / (n : ℝ)) • gram X S)⁻¹

/-- **ℓ∞ error bound** `B(λ;X)` of Theorem 7.21(c) (Wainwright 7.45):
`B(λ;X) = ‖(XₛᵀXₛ/n)⁻¹ Xₛᵀ w/n‖_∞ + |||(XₛᵀXₛ/n)⁻¹|||_∞ · λ`. -/
noncomputable def supportRecoveryBound (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : ℝ :=
  (⨆ i : {x // x ∈ S},
    |((gramInvNorm X S).mulVec
        ((1 / (n : ℝ)) • (Xsub X S)ᵀ.mulVec w.ofLp)) i|)
  + matLinftyNorm (gramInvNorm X S) * lam

/-- The quantity `‖Xₛᶜᵀ Π_{S⊥}(X) (w/n)‖_∞` appearing on the RHS of the regularization
condition (7.44). The condition is `λ ≥ (2/(1−α)) · projNoiseLinf X S w`. -/
noncomputable def projNoiseLinf (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ j : {x // x ∈ Sᶜ},
    |((Xsub X Sᶜ)ᵀ.mulVec ((1 / (n : ℝ)) • (projPerp X S).mulVec w.ofLp)) j|

end StatLean.HighDimensionalStatistics
