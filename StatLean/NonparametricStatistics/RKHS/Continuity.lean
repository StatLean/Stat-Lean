import StatLean.NonparametricStatistics.RKHS.Basic

/-!
# Continuity of the functions in an RKHS with continuous kernel

If `X` is a topological space and the reproducing kernel `K : X × X → 𝕜` is (jointly)
continuous, then:
* the kernel-function map `x ↦ k_x ∈ H` is continuous, via the identity
  `‖k_y − k_{y₀}‖² = K(y,y) − K(y,y₀) − K(y₀,y) + K(y₀,y₀)`; and
* every `f ∈ H` is a continuous function on `X`, since
  `|f(y) − f(y₀)| ≤ ‖f‖·‖k_y − k_{y₀}‖`.

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), §I.5.
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (H) in
/-- Norm identity for differences of kernel functions:
`‖k_y − k_{y₀}‖² = re (K(y,y) − K(y,y₀) − K(y₀,y) + K(y₀,y₀))`. -/
theorem norm_kernelFun_sub_sq (y y₀ : X) :
    ‖kernelFun H y - kernelFun H y₀‖ ^ 2
      = RCLike.re (scalarKernel H y y - scalarKernel H y y₀
          - scalarKernel H y₀ y + scalarKernel H y₀ y₀) := by
  sorry

variable (H) in
/-- If the kernel is jointly continuous then the kernel-function map `x ↦ k_x` is
continuous from `X` to `H`. -/
theorem continuous_kernelFun
    -- USER-INPUT: joint continuity of the reproducing kernel
    (hK : Continuous fun p : X × X => scalarKernel H p.1 p.2) :
    Continuous fun x : X => kernelFun H x := by
  sorry

/-- **Continuous kernels have continuous functions**: if the reproducing kernel of `H` is
jointly continuous on `X × X`, every member of `H` is a continuous function. -/
theorem continuous_coe_of_continuous_scalarKernel
    -- USER-INPUT: joint continuity of the reproducing kernel
    (hK : Continuous fun p : X × X => scalarKernel H p.1 p.2) (f : H) :
    Continuous (f : X → 𝕜) := by
  sorry

end StatLean.NonparametricStatistics
