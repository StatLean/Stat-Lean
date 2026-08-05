import StatLean.NonparametricStatistics.RKHS.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Sobolev space `H₀¹[0,1]` as a reproducing kernel Hilbert space

The classical Sobolev space of absolutely continuous `f : [0,1] → ℝ` with
square-integrable derivative and `f(0) = f(1) = 0`, under the Dirichlet inner product
`⟪f, g⟫ = ∫₀¹ f' g'`, is an RKHS whose kernel is the Green's function of `−d²/dt²` with
Dirichlet boundary conditions:
`K(x, y) = min x y − x y = (1 − max x y) · min x y`.

**Model.** Since `f(x) = ∫₀ˣ f'` characterizes absolutely continuous functions, we take
the *integral representation as the definition*: the carrier is the closed subspace
`{g ∈ L²[0,1] : ∫₀¹ g = 0}` (the orthogonal complement of the constants), an element `g`
acting as the function `x ↦ ∫₀ˣ g = ⟪𝟙_{[0,x]}, g⟫`.  The Dirichlet inner product on the
functions is then the `L²` inner product of the representatives, evaluation is bounded
with `‖E_x‖² = x(1−x)`, and the kernel function of `x` is the representative
`𝟙_{[0,x]} − x·𝟙` (whose primitive is the Green's function above).  Completeness is
inherited from `L²` — this replaces the classical pointwise-Cauchy argument.

**Bibliographic comments.** The Green's-function kernel of the Dirichlet Sobolev space
is classical; see N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), §II.5, and
S. Bergman's earlier work on kernels of differential operators.  This space is the
Cameron–Martin space of the Brownian bridge (R. H. Cameron and W. T. Martin, 1947).
-/

open RKHS MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

/-- The base interval `[0,1]` of the Sobolev space, as the domain of its functions. -/
abbrev unitInterval01 : Set ℝ := Set.Icc 0 1

/-- Lebesgue measure restricted to `[0,1]`. -/
noncomputable abbrev sobolevMeasure : Measure ℝ := volume.restrict unitInterval01

instance : Fact ((volume : Measure ℝ) unitInterval01 < ⊤) :=
  ⟨by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩

/-- The constant function `1` as an element of `L²[0,1]`. -/
noncomputable def sobolevOne : Lp ℝ 2 sobolevMeasure :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℝ)

/-- The indicator `𝟙_{[0,x]}` as an element of `L²[0,1]`; the "derivative" of the ramp
`t ↦ min t x`. -/
noncomputable def sobolevInd (x : ℝ) : Lp ℝ 2 sobolevMeasure :=
  indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := x)) (measure_ne_top _ _) (1 : ℝ)

/-- **The Dirichlet–Sobolev space `H₀¹[0,1]`**, modeled as the mean-zero subspace of
`L²[0,1]` carrying the derivative representative of each function; the boundary
conditions `f(0) = f(1) = 0` correspond to the mean-zero constraint. -/
noncomputable abbrev SobolevH01 : Type _ := ↥((ℝ ∙ sobolevOne)ᗮ)

/-- The Sobolev space is an RKHS on `[0,1]`: the element with derivative representative
`g` acts as the function `x ↦ ∫₀ˣ g = ⟪𝟙_{[0,x]}, g⟫`. -/
noncomputable instance : RKHS ℝ SobolevH01 unitInterval01 ℝ where
  coeCLM :=
    (ContinuousLinearMap.pi fun x : unitInterval01 => innerSL ℝ (sobolevInd x.1)).comp
      (Submodule.subtypeL _)
  coeCLM_injective := by
    sorry

/-- Interpretation of the action: `f x = ∫_{[0,x]} g` where `g` is the derivative
representative of `f`. -/
theorem sobolevH01_apply (f : SobolevH01) (x : unitInterval01) :
    f x = ∫ t in Set.Icc 0 (x : ℝ), ((f : Lp ℝ 2 sobolevMeasure) : ℝ → ℝ) t
      ∂sobolevMeasure := by
  sorry

/-- Left boundary condition: every function of the Sobolev space vanishes at `0`. -/
theorem sobolevH01_apply_zero (f : SobolevH01) :
    f (⟨0, by norm_num⟩ : unitInterval01) = 0 := by
  sorry

/-- Right boundary condition: every function of the Sobolev space vanishes at `1`
(this is where the mean-zero constraint enters). -/
theorem sobolevH01_apply_one (f : SobolevH01) :
    f (⟨1, by norm_num⟩ : unitInterval01) = 0 := by
  sorry

/-- The kernel function of the point `x` has derivative representative
`𝟙_{[0,x]} − x·𝟙` (the formal solution of the Dirichlet boundary-value problem
`−k'' = δₓ`). -/
theorem sobolevH01_kernelFun (x : unitInterval01) :
    (kernelFun SobolevH01 x : Lp ℝ 2 sobolevMeasure)
      = sobolevInd x.1 - (x : ℝ) • sobolevOne := by
  sorry

/-- **The reproducing kernel of `H₀¹[0,1]` is the Dirichlet Green's function**:
`K(x, y) = min x y − x y`. -/
theorem sobolevH01_scalarKernel (x y : unitInterval01) :
    scalarKernel SobolevH01 x y = min (x : ℝ) y - (x : ℝ) * y := by
  sorry

/-- The Green's function in case-split form: `(1−y)x` for `x ≤ y`, `(1−x)y` otherwise. -/
theorem min_sub_mul_eq_ite (x y : ℝ) :
    min x y - x * y = if x ≤ y then (1 - y) * x else (1 - x) * y := by
  sorry

/-- The exact norm of evaluation on the Sobolev space: `‖E_x‖² = ‖k_x‖² = x(1−x)`. -/
theorem sobolevH01_norm_kernelFun_sq (x : unitInterval01) :
    ‖kernelFun SobolevH01 x‖ ^ 2 = (x : ℝ) * (1 - (x : ℝ)) := by
  sorry

/-- The sharp evaluation bound on the Sobolev space:
`|f(x)| ≤ √(x(1−x)) · ‖f‖` — improving the naive Cauchy–Schwarz bound `√x · ‖f‖`. -/
theorem sobolevH01_norm_apply_le (f : SobolevH01) (x : unitInterval01) :
    ‖f x‖ ≤ Real.sqrt ((x : ℝ) * (1 - (x : ℝ))) * ‖f‖ := by
  sorry

end StatLean.NonparametricStatistics
