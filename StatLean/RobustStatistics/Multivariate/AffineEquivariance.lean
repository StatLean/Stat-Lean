import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Affine equivariance of multivariate location and scatter functionals

The interface layer for multivariate robust statistics (`MMY §6.17.1`, "Why affine
equivariance?"): a multivariate location functional should follow affine maps,
`T((Ax+b)_\#P) = A\,T(P) + b`, and a scatter functional should transform as
`S((Ax+b)_\#P) = A\,S(P)\,A^\top`. The mean vector and the covariance matrix are the
sanity-check instances; the high-breakdown multivariate estimators of `MMY §6` are
deferred to a later round.

Vectors are coordinate functions `Fin d → ℝ` and affine maps act through `Matrix.mulVec`,
avoiding inner-product-space packaging.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §6.2, §6.17.1.
-/

open MeasureTheory

namespace StatLean.RobustStatistics

variable {d : ℕ}

/-- **Affine equivariance of a multivariate location functional** on a domain class
(`MMY §6.17.1`): `T((Ax+b)_#P) = A T(P) + b` for every invertible `A`. -/
def IsAffineEquivariantLocation (T : Measure (Fin d → ℝ) → (Fin d → ℝ))
    (𝒫 : Set (Measure (Fin d → ℝ))) : Prop :=
  ∀ P ∈ 𝒫, ∀ A : Matrix (Fin d) (Fin d) ℝ, IsUnit A.det → ∀ b : Fin d → ℝ,
    T (P.map fun x => A.mulVec x + b) = A.mulVec (T P) + b

/-- **Affine equivariance of a scatter functional** on a domain class (`MMY §6.17.1`):
`S((Ax+b)_#P) = A S(P) Aᵀ`. -/
def IsAffineEquivariantScatter (S : Measure (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (𝒫 : Set (Measure (Fin d → ℝ))) : Prop :=
  ∀ P ∈ 𝒫, ∀ A : Matrix (Fin d) (Fin d) ℝ, IsUnit A.det → ∀ b : Fin d → ℝ,
    S (P.map fun x => A.mulVec x + b) = A * S P * A.transpose

/-- The **mean vector functional**, coordinatewise (`MMY §6.1` context). Junk value `0`
in non-integrable coordinates. -/
noncomputable def meanVecFunctional (P : Measure (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => ∫ x, x i ∂P

/-- The **covariance matrix functional** (`MMY §6.1` context). -/
noncomputable def covMatrixFunctional (P : Measure (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    ∫ x, (x i - meanVecFunctional P i) * (x j - meanVecFunctional P j) ∂P

/-- **The mean vector is affine equivariant** (`MMY §6.17.1`, sanity check) on
probability measures with integrable coordinates. -/
theorem meanVecFunctional_affineEquivariant :
    IsAffineEquivariantLocation (meanVecFunctional (d := d))
      {P | IsProbabilityMeasure P ∧ ∀ i, Integrable (fun x => x i) P} := by
  sorry

/-- **The covariance matrix is affine equivariant scatter** (`MMY §6.17.1`, sanity
check) on probability measures with square-integrable coordinates. -/
theorem covMatrixFunctional_affineEquivariant :
    IsAffineEquivariantScatter (covMatrixFunctional (d := d))
      {P | IsProbabilityMeasure P ∧ ∀ i, MemLp (fun x => x i) 2 P} := by
  sorry

end StatLean.RobustStatistics
