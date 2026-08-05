import StatLean.NonparametricStatistics.RKHS.KernelFunction
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The all-ones matrix and the min kernel

Two classical positivity computations:

* the `n × n` all-ones matrix `Jₙ` is positive semidefinite, has eigenvalue `n` (on the
  constant vector), every eigenvalue is `0` or `n`, and has rank one;
* the function `K(x, y) = min x y` on `[0, ∞)` is a kernel function.  Rather than the
  inductive block decomposition, we exhibit `min` as the Gram function of the feature map
  `x ↦ 𝟙_{[0,x]} ∈ L²([0,∞))`, since `∫ 𝟙_{[0,x]} 𝟙_{[0,y]} = min x y`.

The RKHS of the min kernel (Cameron–Martin space of Brownian motion) is identified with
the range of the Volterra operator in `RangeSpace.lean`.

**Bibliographic comments.** The min kernel is the covariance of Brownian motion
(N. Wiener 1923); its RKHS was identified by R. H. Cameron and W. T. Martin, Ann. of
Math. **48** (1947), 385–392, and the general covariance–RKHS correspondence is due to
M. Loève and E. Parzen, *Statistical inference on time series by Hilbert space methods*
(1959).
-/

open ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]

section AllOnes

variable (𝕜) in
/-- The `n × n` all-ones matrix `Jₙ`. -/
def allOnesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun _ _ => 1

/-- The all-ones matrix is positive semidefinite: its quadratic form is `|∑ αᵢ|²`. -/
theorem posSemidef_allOnesMatrix (n : ℕ) : (allOnesMatrix 𝕜 n).PosSemidef := by
  sorry

/-- `n` is an eigenvalue of the all-ones matrix `Jₙ` (witnessed by the constant vector),
for `n ≥ 1`. -/
theorem hasEigenvalue_allOnesMatrix (n : ℕ)
    -- LEAN-ONLY: nonempty index type; for `n = 0` there are no eigenvectors at all
    (hn : 0 < n) :
    Module.End.HasEigenvalue (Matrix.toLin' (allOnesMatrix 𝕜 n)) (n : 𝕜) := by
  sorry

/-- Every eigenvalue of the all-ones matrix is `0` or `n` (since `Jₙ² = n·Jₙ`). -/
theorem eigenvalue_allOnesMatrix (n : ℕ) (μ : 𝕜)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (allOnesMatrix 𝕜 n)) μ) :
    μ = 0 ∨ μ = (n : 𝕜) := by
  sorry

/-- The all-ones matrix has rank one (`n ≥ 1`): the eigenvalue `n` has multiplicity one. -/
theorem rank_allOnesMatrix (n : ℕ)
    -- LEAN-ONLY: nonempty index type; `J₀` has rank zero
    (hn : 0 < n) :
    (allOnesMatrix 𝕜 n).rank = 1 := by
  sorry

end AllOnes

section MinKernel

/-- `min x y = ∫ 𝟙_{[0,x]} · 𝟙_{[0,y]}` over `[0, ∞)`: the min kernel is the Gram
function of indicator feature vectors. -/
theorem min_eq_integral_indicator (x y : ℝ)
    -- USER-INPUT: the points lie in `[0, ∞)`
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y
      = ∫ t, Set.indicator (Set.Icc 0 x) (fun _ => (1 : ℝ)) t
          * Set.indicator (Set.Icc 0 y) (fun _ => (1 : ℝ)) t := by
  sorry

/-- **The min kernel is a kernel function** on `[0, ∞)`. -/
theorem isKernelFun_min :
    IsKernelFun fun x y : Set.Ici (0 : ℝ) => min x.1 y.1 := by
  sorry

end MinKernel

end StatLean.NonparametricStatistics
