import StatLean.NonparametricStatistics.RKHS.KernelFunction
import StatLean.NonparametricStatistics.RKHS.Moore

/-!
# Feature maps and the kernel method

A **feature map** is an embedding `φ : X → L` of the data domain into an auxiliary
Hilbert space; it induces the kernel `K(x, y) = ⟪φ x, φ y⟫` on `X` (`featureKernel`,
defined in `KernelFunction.lean`, where it is shown to be a kernel function).  This file
records the two directions of the "kernel trick":

* every RKHS kernel arises from a feature map — namely its own kernel functions
  (`scalarKernel_eq_featureKernel`, restated here);
* every kernel induced by a feature map is the reproducing kernel of an RKHS
  (via Moore's theorem), so optimizing over the induced function class is optimizing
  over an RKHS.

**Bibliographic comments.** The kernel trick in statistical learning goes back to
M. Aizerman, E. Braverman and L. Rozonoer, *Theoretical foundations of the potential
function method*, Autom. Remote Control **25** (1964), 821–837, and was popularized by
B. E. Boser, I. M. Guyon and V. N. Vapnik, *A training algorithm for optimal margin
classifiers*, COLT (1992).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

/-- A feature-map kernel is Hermitian-diagonal-normalized: `K(x,x) = ‖φ x‖²`. -/
theorem featureKernel_self (φ : X → L) (x : X) :
    featureKernel 𝕜 φ x x = ((‖φ x‖ : 𝕜)) ^ 2 := by
  sorry

/-- **Every kernel function is a feature-map kernel**: by Moore's theorem, a kernel
function `K` is the Gram function of the kernel-function embedding of its RKHS. -/
theorem IsKernelFun.exists_featureMap {K : X → X → 𝕜} (hK : IsKernelFun K) :
    ∃ (L' : Type _) (_ : NormedAddCommGroup L') (_ : InnerProductSpace 𝕜 L')
      (φ : X → L'), K = featureKernel 𝕜 φ := by
  sorry

/-- The predictor class of a feature map: functions of the form `x ↦ ⟪φ x, w⟫` for
`w ∈ L` — the "linear functionals in feature space". -/
def featurePredictor (φ : X → L) (w : L) : X → 𝕜 := fun x => ⟪φ x, w⟫_𝕜

/-- Predictors are pointwise-bounded by the kernel diagonal:
`‖(featurePredictor φ w) x‖ ≤ √(re K(x,x)) · ‖w‖`. -/
theorem norm_featurePredictor_le (φ : X → L) (w : L) (x : X) :
    ‖featurePredictor φ w x‖
      ≤ Real.sqrt (RCLike.re (featureKernel 𝕜 φ x x)) * ‖w‖ := by
  sorry

end StatLean.NonparametricStatistics
