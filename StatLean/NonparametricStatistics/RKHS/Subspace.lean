import StatLean.NonparametricStatistics.RKHS.Basic

/-!
# Closed subspaces of an RKHS are RKHSs

A closed subspace `H₀` of a scalar RKHS `H` on `X` is again an RKHS on `X` (evaluation
functionals stay bounded under restriction), and its kernel is the projection of the
ambient kernel: `K₀(x, y) = (P₀ k_y)(x) = ⟪P₀ k_y, k_x⟫`, where `P₀` is the orthogonal
projection onto `H₀`.  In particular `kernelFun H₀ x = P₀ (kernelFun H x)`.

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950),
§I.9 (kernels of subspaces and differences of kernels).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- A (complete, i.e. closed) subspace of an RKHS is an RKHS on the same set, with the
restricted evaluation. -/
noncomputable instance Submodule.instRKHS (H₀ : Submodule 𝕜 H) : RKHS 𝕜 H₀ X 𝕜 where
  coeCLM := (coeCLM 𝕜).comp H₀.subtypeL
  coeCLM_injective := by
    sorry

/-- Evaluation in the subspace RKHS agrees with evaluation in the ambient space. -/
@[simp]
theorem coe_submodule_apply (H₀ : Submodule 𝕜 H) (f : H₀) (x : X) :
    f x = (f : H) x := rfl

/-- The kernel function of a closed subspace is the orthogonal projection of the ambient
kernel function: `kernelFun H₀ x = P₀ (kernelFun H x)`. -/
theorem kernelFun_submodule (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x : X) :
    (kernelFun H₀ x : H) = H₀.starProjection (kernelFun H x) := by
  sorry

/-- **The kernel of a closed subspace**: `K₀(x, y) = (P₀ k_y)(x)`, the projected ambient
kernel function evaluated at the point. -/
theorem scalarKernel_submodule (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x y : X) :
    scalarKernel H₀ x y = (H₀.starProjection (kernelFun H y)) x := by
  sorry

/-- The kernel of a closed subspace as an inner product against the ambient kernel
function: `K₀(x, y) = ⟪k_x, P₀ k_y⟫`. -/
theorem scalarKernel_submodule_inner (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x y : X) :
    scalarKernel H₀ x y
      = ⟪kernelFun H x, H₀.starProjection (kernelFun H y)⟫_𝕜 := by
  sorry

end StatLean.NonparametricStatistics
