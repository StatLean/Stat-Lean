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

instance : IsClosed (((ℝ ∙ sobolevOne)ᗮ : Submodule ℝ (Lp ℝ 2 sobolevMeasure)) :
    Set (Lp ℝ 2 sobolevMeasure)) :=
  Submodule.isClosed_orthogonal _

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

section Aux

/-- The measure of `[0,m]` inside `[0,1]`, as a real number. -/
private theorem sobolevMeasure_real_Icc {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    sobolevMeasure.real (Set.Icc 0 m) = m := by
  change ((volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc 0 m)).toReal = m
  rw [Measure.restrict_apply measurableSet_Icc, Set.Icc_inter_Icc, max_self, min_eq_left hm1,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hm0]

/-- The total mass of `sobolevMeasure` is one. -/
private theorem sobolevMeasure_real_univ : sobolevMeasure.real Set.univ = 1 := by
  change ((volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ).toReal = 1
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  norm_num

/-- Restricting `sobolevMeasure` to `[0,1]` changes nothing. -/
private theorem sobolevMeasure_restrict_Icc :
    sobolevMeasure.restrict (Set.Icc (0 : ℝ) 1) = sobolevMeasure := by
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Icc (0 : ℝ) 1) = _
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_self]

private theorem inner_sobolevInd_sobolevInd {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) :
    ⟪sobolevInd x, sobolevInd y⟫_ℝ = min x y := by
  rw [sobolevInd, sobolevInd,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := sobolevMeasure) (measurableSet_Icc (a := (0 : ℝ)) (b := x))
      (measurableSet_Icc (a := (0 : ℝ)) (b := y)) (measure_ne_top _ _) (measure_ne_top _ _),
    Set.Icc_inter_Icc, max_self,
    sobolevMeasure_real_Icc (le_min hx0 hy0) ((min_le_left x y).trans hx1)]

private theorem inner_sobolevOne_sobolevInd {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ⟪sobolevOne, sobolevInd y⟫_ℝ = y := by
  rw [sobolevOne, sobolevInd,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := sobolevMeasure) MeasurableSet.univ (measurableSet_Icc (a := (0 : ℝ)) (b := y))
      (measure_ne_top _ _) (measure_ne_top _ _),
    Set.univ_inter, sobolevMeasure_real_Icc hy0 hy1]

private theorem inner_sobolevInd_sobolevOne {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ⟪sobolevInd y, sobolevOne⟫_ℝ = y := by
  rw [real_inner_comm, inner_sobolevOne_sobolevInd hy0 hy1]

private theorem inner_sobolevOne_sobolevOne : ⟪sobolevOne, sobolevOne⟫_ℝ = 1 := by
  rw [sobolevOne,
    MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := sobolevMeasure) MeasurableSet.univ MeasurableSet.univ
      (measure_ne_top _ _) (measure_ne_top _ _),
    Set.univ_inter, sobolevMeasure_real_univ]

private theorem inner_sobolevInd_eq_setIntegral (x : ℝ) (g : Lp ℝ 2 sobolevMeasure) :
    ⟪sobolevInd x, g⟫_ℝ = ∫ t in Set.Icc 0 x, (g : ℝ → ℝ) t ∂sobolevMeasure :=
  MeasureTheory.L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := sobolevMeasure)
    (measurableSet_Icc (a := (0 : ℝ)) (b := x)) (measure_ne_top _ _) g

private theorem inner_sobolevOne_eq_integral (g : Lp ℝ 2 sobolevMeasure) :
    ⟪sobolevOne, g⟫_ℝ = ∫ t, (g : ℝ → ℝ) t ∂sobolevMeasure := by
  rw [← MeasureTheory.setIntegral_univ]
  exact MeasureTheory.L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := sobolevMeasure)
    MeasurableSet.univ (measure_ne_top _ _) g

/-- Unfolding of the RKHS action of the Sobolev space. -/
private theorem sobolevH01_coe_apply (f : SobolevH01) (x : unitInterval01) :
    f x = ⟪sobolevInd (x : ℝ), (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ := rfl

/-- The `[0,1]`-indicator and the constant `1` have the same action on `L²[0,1]`. -/
private theorem inner_sobolevInd_one_eq (g : Lp ℝ 2 sobolevMeasure) :
    ⟪sobolevInd (1 : ℝ), g⟫_ℝ = ⟪sobolevOne, g⟫_ℝ := by
  rw [inner_sobolevInd_eq_setIntegral, inner_sobolevOne_eq_integral, sobolevMeasure_restrict_Icc]

end Aux

/-- Interpretation of the action: `f x = ∫_{[0,x]} g` where `g` is the derivative
representative of `f`. -/
theorem sobolevH01_apply (f : SobolevH01) (x : unitInterval01) :
    f x = ∫ t in Set.Icc 0 (x : ℝ), ((f : Lp ℝ 2 sobolevMeasure) : ℝ → ℝ) t
      ∂sobolevMeasure := by
  rw [sobolevH01_coe_apply, inner_sobolevInd_eq_setIntegral]

/-- Left boundary condition: every function of the Sobolev space vanishes at `0`. -/
theorem sobolevH01_apply_zero (f : SobolevH01) :
    f (⟨0, by norm_num⟩ : unitInterval01) = 0 := by
  rw [sobolevH01_apply]
  refine setIntegral_measure_zero _ ?_
  change (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc 0 (0 : ℝ)) = 0
  rw [Set.Icc_self, Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null Set.inter_subset_left (by simp)

/-- Right boundary condition: every function of the Sobolev space vanishes at `1`
(this is where the mean-zero constraint enters). -/
theorem sobolevH01_apply_one (f : SobolevH01) :
    f (⟨1, by norm_num⟩ : unitInterval01) = 0 := by
  rw [sobolevH01_coe_apply]
  change ⟪sobolevInd (1 : ℝ), (f : Lp ℝ 2 sobolevMeasure)⟫_ℝ = 0
  rw [inner_sobolevInd_one_eq]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp f.2

/-- Completeness of the Sobolev carrier, as an explicit term (the orthogonal complement
of a subspace of the complete space `L²` is complete). -/
@[reducible]
noncomputable def sobolevH01CompleteSpace : CompleteSpace SobolevH01 :=
  Submodule.instOrthogonalCompleteSpace (ℝ ∙ sobolevOne)

/-- The kernel function of the Sobolev space at `x` (the completeness instance is passed
explicitly; definitionally `kernelFun SobolevH01 x`). -/
noncomputable def sobolevKernelFun (x : unitInterval01) : SobolevH01 :=
  @kernelFun ℝ _ unitInterval01 SobolevH01 _ _ sobolevH01CompleteSpace _ x

/-- The reproducing kernel of the Sobolev space (definitionally
`scalarKernel SobolevH01`). -/
noncomputable def sobolevScalarKernel (x y : unitInterval01) : ℝ :=
  @scalarKernel ℝ _ unitInterval01 SobolevH01 _ _ sobolevH01CompleteSpace _ x y

/-- The kernel function of the point `x` has derivative representative
`𝟙_{[0,x]} − x·𝟙` (the formal solution of the Dirichlet boundary-value problem
`−k'' = δₓ`). -/
theorem sobolevH01_kernelFun (x : unitInterval01) :
    (sobolevKernelFun x : Lp ℝ 2 sobolevMeasure)
      = sobolevInd x.1 - (x : ℝ) • sobolevOne := by
  sorry

/-- **The reproducing kernel of `H₀¹[0,1]` is the Dirichlet Green's function**:
`K(x, y) = min x y − x y`. -/
theorem sobolevH01_scalarKernel (x y : unitInterval01) :
    sobolevScalarKernel x y = min (x : ℝ) y - (x : ℝ) * y := by
  sorry

/-- The Green's function in case-split form: `(1−y)x` for `x ≤ y`, `(1−x)y` otherwise. -/
theorem min_sub_mul_eq_ite (x y : ℝ) :
    min x y - x * y = if x ≤ y then (1 - y) * x else (1 - x) * y := by
  sorry

/-- The exact norm of evaluation on the Sobolev space: `‖E_x‖² = ‖k_x‖² = x(1−x)`. -/
theorem sobolevH01_norm_kernelFun_sq (x : unitInterval01) :
    ‖sobolevKernelFun x‖ ^ 2 = (x : ℝ) * (1 - (x : ℝ)) := by
  sorry

/-- The sharp evaluation bound on the Sobolev space:
`|f(x)| ≤ √(x(1−x)) · ‖f‖` — improving the naive Cauchy–Schwarz bound `√x · ‖f‖`. -/
theorem sobolevH01_norm_apply_le (f : SobolevH01) (x : unitInterval01) :
    ‖f x‖ ≤ Real.sqrt ((x : ℝ) * (1 - (x : ℝ))) * ‖f‖ := by
  sorry

end StatLean.NonparametricStatistics
