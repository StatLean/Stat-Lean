import StatLean.NonparametricStatistics.RKHS.Basic
import StatLean.NonparametricStatistics.RKHS.ParsevalFrame

/-!
# Parseval frames of an RKHS and pointwise kernel expansions

A family `{f_i} ⊆ H` in a scalar RKHS is a Parseval frame **iff** the reproducing kernel
expands pointwise through it: `K(x, y) = ∑ᵢ f_i(x) · conj (f_i y)`.  This generalizes the
orthonormal-basis expansion (`OrthonormalExpansion.lean`) — frames need not be linearly
independent — and is the practical tool for *recognizing* an RKHS from a series
representation of its kernel.

Forward direction: `K(x,y) = ⟪k_x, k_y⟫` and the polarized Parseval identity.  Converse:
the analysis operator is isometric on the dense span of the kernel functions, hence
extends to an isometry, which characterizes Parseval frames.

**Bibliographic comments.** Attributed to M. Papadakis; see M. Papadakis,
*On the dimension function of orthonormal wavelets*, Proc. Amer. Math. Soc. **128**
(2000), 2043–2049, and V. I. Paulsen's course notes on reproducing kernels for this
formulation.
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- A Parseval frame of an RKHS expands the kernel pointwise:
`K(x, y) = ∑ᵢ f_i(x) · conj (f_i y)`. -/
theorem IsParsevalFrame.hasSum_scalarKernel {f : ι → H} (hf : IsParsevalFrame 𝕜 f)
    (x y : X) :
    HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y) := by
  sorry

/-- **Papadakis' criterion**, converse direction: if a family of members of `H` expands
the kernel pointwise, it is a Parseval frame for `H`. -/
theorem isParsevalFrame_of_hasSum_scalarKernel {f : ι → H}
    -- USER-INPUT: pointwise expansion of the kernel through the family
    (hexp : ∀ x y, HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y)) :
    IsParsevalFrame 𝕜 f := by
  sorry

/-- **Papadakis' criterion**: a family in an RKHS is a Parseval frame iff it expands the
reproducing kernel pointwise. -/
theorem isParsevalFrame_iff_hasSum_scalarKernel {f : ι → H} :
    IsParsevalFrame 𝕜 f
      ↔ ∀ x y, HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y) := by
  sorry

end StatLean.NonparametricStatistics
