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
noncomputable def dualRKHS : RKHS 𝕜 L L 𝕜 where
  coeCLM := ContinuousLinearMap.pi fun v => innerSL 𝕜 v
  coeCLM_injective := by
    sorry

/-- Under `dualRKHS`, the kernel function of the point `x ∈ L` is `x` itself. -/
theorem dualRKHS_kernelFun (x : L) :
    letI := dualRKHS 𝕜 L
    kernelFun L x = x := by
  sorry

/-- **The inner product is the reproducing kernel of the dual RKHS**:
`K(x, y) = ⟪x, y⟫_𝕜`. -/
theorem dualRKHS_scalarKernel (x y : L) :
    letI := dualRKHS 𝕜 L
    scalarKernel L x y = ⟪x, y⟫_𝕜 := by
  sorry

/-- The inner product of a Hilbert space is a kernel function on the underlying set. -/
theorem isKernelFun_inner :
    IsKernelFun fun x y : L => ⟪x, y⟫_𝕜 := by
  sorry

/-- Under `dualRKHS`, the functions of the RKHS are exactly the bounded linear
functionals on `L` (Riesz representation). -/
theorem dualRKHS_range_coe :
    letI := dualRKHS 𝕜 L
    Set.range (fun w : L => (w : L → 𝕜)) = {g : L → 𝕜 | ∃ T : L →L[𝕜] 𝕜, g = T} := by
  sorry

end StatLean.NonparametricStatistics
