import StatLean.NonparametricStatistics.RKHS.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Pointwise orthonormal expansion of a reproducing kernel

If `{e_i}` is a Hilbert basis of a scalar RKHS `H` on `X`, then the reproducing kernel
expands pointwise as the unordered sum
`K(x, y) = ∑ᵢ conj (e_i y) · e_i x`,
because `k_y = ∑ᵢ conj (e_i y) · e_i` converges in norm and norm convergence implies
pointwise convergence.  On the diagonal this is the Parseval identity
`K(x, x) = ∑ᵢ ‖e_i x‖²`.

**Bibliographic comments.** The expansion of a reproducing kernel along an orthonormal
basis appears in N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), 337–404, §I.4;
for the Szegő and Bergman kernels it goes back to G. Szegő (1921) and S. Bergman (1922).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- The kernel function of a point expands along a Hilbert basis with coefficients the
conjugated point values: `k_y = ∑ᵢ conj (e_i y) • e_i` (norm convergence, unordered). -/
theorem hasSum_kernelFun (e : HilbertBasis ι 𝕜 H) (y : X) :
    HasSum (fun i => conj ((e i : H) y) • (e i : H)) (kernelFun H y) := by
  sorry

/-- **Pointwise expansion of the kernel along a Hilbert basis**:
`K(x, y) = ∑ᵢ conj (e_i y) · e_i x` as an unordered pointwise sum. -/
theorem hasSum_scalarKernel (e : HilbertBasis ι 𝕜 H) (x y : X) :
    HasSum (fun i => conj ((e i : H) y) * (e i : H) x) (scalarKernel H x y) := by
  sorry

/-- Diagonal (Parseval) form of the kernel expansion: `K(x, x) = ∑ᵢ ‖e_i x‖²`. -/
theorem hasSum_scalarKernel_self (e : HilbertBasis ι 𝕜 H) (x : X) :
    HasSum (fun i => ‖(e i : H) x‖ ^ 2) (RCLike.re (scalarKernel H x x)) := by
  sorry

/-- The point values of a Hilbert basis of an RKHS are square-summable, with sum bounded
by the kernel diagonal. -/
theorem summable_normSq_apply (e : HilbertBasis ι 𝕜 H) (x : X) :
    Summable fun i => ‖(e i : H) x‖ ^ 2 := by
  sorry

end StatLean.NonparametricStatistics
