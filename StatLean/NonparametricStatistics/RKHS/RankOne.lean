import StatLean.NonparametricStatistics.RKHS.KernelFunction

/-!
# The rank-one RKHS induced by a single function

For a function `f₀ : X → 𝕜`, the product `K(x, y) = f₀(x) · conj (f₀ y)` is a kernel
function, and any RKHS with this kernel is the one-dimensional space spanned by `f₀`,
on which `f₀` itself has norm `1` (when `f₀ ≠ 0`).

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), Part I
§2 (elementary examples of reproducing kernels).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}

/-- The rank-one product `K(x, y) = f₀(x) · conj (f₀ y)` of any function with itself is a
kernel function. -/
theorem isKernelFun_rankOne (f₀ : X → 𝕜) :
    IsKernelFun fun x y => f₀ x * conj (f₀ y) := by
  sorry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- **The RKHS of a rank-one kernel is one-dimensional**: if the kernel of `H` is
`f₀(x) · conj (f₀ y)` with `f₀ ≠ 0`, then `H` is spanned by a single unit vector whose
underlying function is `f₀`. -/
theorem exists_unit_spanning_of_scalarKernel_rankOne (f₀ : X → 𝕜)
    -- USER-INPUT: the generating function is not identically zero
    (hf₀ : f₀ ≠ 0)
    -- USER-INPUT: the kernel of `H` is the rank-one product of `f₀`
    (hK : scalarKernel H = fun x y => f₀ x * conj (f₀ y)) :
    ∃ g : H, (g : X → 𝕜) = f₀ ∧ ‖g‖ = 1 ∧ ∀ h : H, ∃ c : 𝕜, h = c • g := by
  sorry

/-- The kernel functions of a rank-one RKHS: `k_y = conj (f₀ y) • g` where `g` is the
unit vector representing `f₀`. -/
theorem kernelFun_of_scalarKernel_rankOne (f₀ : X → 𝕜)
    -- USER-INPUT: the kernel of `H` is the rank-one product of `f₀`
    (hK : scalarKernel H = fun x y => f₀ x * conj (f₀ y))
    {g : H} (hg : (g : X → 𝕜) = f₀) (hgnorm : ‖g‖ = 1) (y : X) :
    kernelFun H y = conj (f₀ y) • g := by
  sorry

end StatLean.NonparametricStatistics
