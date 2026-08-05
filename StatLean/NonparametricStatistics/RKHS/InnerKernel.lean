import StatLean.NonparametricStatistics.RKHS.KernelFunction

/-!
# The RKHS induced by the inner product of a Hilbert space

For a Hilbert space `L`, the inner product `K(x, y) = ⟪x, y⟫` is a kernel function on the
set `L`, and the corresponding RKHS is the space of bounded linear functionals of the
form `v ↦ ⟪v, w⟫` — i.e. `L` itself, acting on `L` through the (anti-)duality.  We
realize this concretely: `L` carries an RKHS structure over the set `X = L` with
`coeCLM w = fun v => ⟪v, w⟫_𝕜`, under which the kernel function of the point `x` is `x`
itself and the reproducing kernel is the inner product.

The structure is provided as a `def` (`dualRKHS`), not a global instance: making every
Hilbert space coerce to functions on itself would pollute downstream elaboration.

**Bibliographic comments.** This is the Riesz–Fréchet representation theorem (F. Riesz
1907, M. Fréchet 1907) read as a statement about reproducing kernels; see also
N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), §I.3.
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable (𝕜 : Type*) [RCLike 𝕜]
variable (L : Type*) [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/-- The RKHS structure on a Hilbert space `L` over the set `L` itself, where the element
`w` acts as the bounded functional `v ↦ ⟪v, w⟫_𝕜`.  Not an instance by design. -/
@[reducible]
noncomputable def dualRKHS : RKHS 𝕜 L L 𝕜 where
  coeCLM := ContinuousLinearMap.pi fun v => innerSL 𝕜 v
  coeCLM_injective := by
    intro w₁ w₂ h
    refine ext_inner_left 𝕜 fun v => ?_
    simpa using congrFun h v

/-- Under `dualRKHS`, the kernel function of the point `x ∈ L` is `x` itself. -/
theorem dualRKHS_kernelFun (x : L) :
    letI := dualRKHS 𝕜 L
    kernelFun L x = x := by
  letI := dualRKHS 𝕜 L
  refine ext_inner_right 𝕜 fun f => ?_
  rw [inner_kernelFun]
  rfl

/-- **The inner product is the reproducing kernel of the dual RKHS**:
`K(x, y) = ⟪x, y⟫_𝕜`. -/
theorem dualRKHS_scalarKernel (x y : L) :
    letI := dualRKHS 𝕜 L
    scalarKernel L x y = ⟪x, y⟫_𝕜 := by
  letI := dualRKHS 𝕜 L
  show (kernelFun L y) x = ⟪x, y⟫_𝕜
  rw [dualRKHS_kernelFun]
  rfl

/-- The inner product of a Hilbert space is a kernel function on the underlying set. -/
theorem isKernelFun_inner :
    IsKernelFun fun x y : L => ⟪x, y⟫_𝕜 :=
  isKernelFun_featureKernel (𝕜 := 𝕜) (E := L) (X := L) id

/-- Machine-checked witness that `dualRKHS_range_coe` is FALSE over `𝕜 = ℂ`.

`coeCLM` must be `𝕜`-*linear* in the RKHS element, and Mathlib's inner product is linear in
its *second* slot; hence the element `w` is forced into the second slot and the function it
represents is `v ↦ ⟪v, w⟫_𝕜`, which is *conjugate*-linear in `v`.  So the range of the
coercion is the set of continuous conjugate-linear functionals, not the linear ones.

Witness: `L = 𝕜 = ℂ`, `w = 1`, whose function is `conj`.  If `conj = ⇑T` for some
`T : ℂ →L[ℂ] ℂ` then `T 1 = 1`, so `T I = I • T 1 = I`, while `conj I = -I`. -/
private theorem dualRKHS_range_coe_false :
    letI := dualRKHS ℂ ℂ
    Set.range (fun w : ℂ => (w : ℂ → ℂ)) ≠ {g : ℂ → ℂ | ∃ T : ℂ →L[ℂ] ℂ, g = T} := by
  letI := dualRKHS ℂ ℂ
  intro h
  have hmem : (fun v : ℂ => conj v) ∈ Set.range (fun w : ℂ => (w : ℂ → ℂ)) := by
    refine ⟨1, ?_⟩
    funext v
    show ⟪v, (1 : ℂ)⟫_ℂ = conj v
    rw [RCLike.inner_apply, one_mul]
  rw [h] at hmem
  obtain ⟨T, hT⟩ := hmem
  have h1 : T 1 = (1 : ℂ) := by
    have := congrFun hT 1
    simpa using this.symm
  have hI : T Complex.I = -Complex.I := by
    have := congrFun hT Complex.I
    simpa using this.symm
  have h2 : T Complex.I = Complex.I := by
    have hs : Complex.I • (1 : ℂ) = Complex.I := by simp
    rw [← hs, map_smul, h1, smul_eq_mul, mul_one]
  rw [hI] at h2
  exact Complex.I_ne_zero (by linear_combination -h2 / 2)

/-- Under `dualRKHS`, the functions of the RKHS are exactly the bounded linear
functionals on `L` (Riesz representation).

OBSTRUCTION (see `dualRKHS_range_coe_false` just above): this statement is FALSE for
`𝕜 = ℂ`.  The elements of `dualRKHS 𝕜 L` are the functions `v ↦ ⟪v, w⟫_𝕜`, which are
continuous *conjugate*-linear functionals; over `ℂ` these are not the `ℂ`-linear ones.
The direction of the anti-linearity is forced: `RKHS.coeCLM` is required to be
`𝕜`-linear in the RKHS element, and Mathlib's `⟪·,·⟫_𝕜` is linear in the second slot
only, so the element must occupy the second slot.  Repairing the statement would mean
replacing `L →L[𝕜] 𝕜` by the continuous conjugate-linear maps `L →L⋆[𝕜] 𝕜`
(i.e. `Set.range (fun w : L => (w : L → 𝕜)) = {g | ∃ T : L →L⋆[𝕜] 𝕜, g = T}`, which is
Riesz–Fréchet); the statement is frozen, so the `sorry` is left in place. -/
theorem dualRKHS_range_coe :
    letI := dualRKHS 𝕜 L
    Set.range (fun w : L => (w : L → 𝕜)) = {g : L → 𝕜 | ∃ T : L →L[𝕜] 𝕜, g = T} := by
  sorry

end StatLean.NonparametricStatistics
