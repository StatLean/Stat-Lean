import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Fixed-design linear model — definitions

Book setup (Lu, *Big Data Analysis* §5): a fixed design matrix `X ∈ ℝ^{n×d}`,
response `Y = X β* + ε ∈ ℝ^n`, and the ordinary least-squares estimator
`β̂^{LS}` defined as a **minimiser** of the residual sum of squares
`‖Y − X β‖²` (the "zero-order condition", not the closed form `(XᵀX)⁻¹XᵀY`,
which need not exist when `X` is rank-deficient — exactly the regime of the OLS
MSE theorem `thm:mse-ols`).

Vectors live in `EuclideanSpace ℝ (Fin ·)` (the ℓ²/inner-product space used
throughout the library). The design matrix acts as the linear map
`Matrix.toEuclideanLin X : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)`.
These are concept-layer, theorem-agnostic definitions consumed by
`OLS/MSEExpectation.lean` and `OLS/MSEHighProb.lean`.
-/

open Matrix MeasureTheory

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- The design map `E^d → E^n` induced by the design matrix `X` (Lu §5):
`β ↦ X β`, as a continuous linear-algebraic map between Euclidean spaces. -/
noncomputable def designMap (X : Matrix (Fin n) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin X

/-- **Prediction mean squared error** `MSE(X β̂) = (1/n) ‖X β̂ − X β*‖²`
(Lu §5, `thm:mse-ols`). Degenerate `n = 0` gives `0` (the `1/n` factor is `0`). -/
noncomputable def mse (X : Matrix (Fin n) (Fin d) ℝ)
    (β βstar : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ‖designMap X β - designMap X βstar‖ ^ 2

/-- **OLS estimator predicate** (Lu §5): `β̂` is a least-squares estimator for
response `Y` under design `X` iff it minimises the residual sum of squares
`‖Y − X β‖²` over all `β`. This is the zero-order (minimiser) characterisation,
deliberately *not* a closed form, so it is well-defined for rank-deficient `X`. -/
def IsOLSEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (βhat : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ β, ‖Y - designMap X βhat‖ ^ 2 ≤ ‖Y - designMap X β‖ ^ 2

/-- **Column space** `C(X)` of the design (Lu §5): the range of the design map,
a subspace of `E^n`. The book's `r = rank(X)` is its dimension. -/
noncomputable def columnSpace (X : Matrix (Fin n) (Fin d) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (designMap X)

/-- The book's design rank `r = rank(X)` (Lu §5, `thm:mse-ols`). Equal to the
dimension of the column space; here taken as `Matrix.rank X`. -/
noncomputable def designRank (X : Matrix (Fin n) (Fin d) ℝ) : ℕ :=
  X.rank

end StatLean.HighDimensionalStatistics
