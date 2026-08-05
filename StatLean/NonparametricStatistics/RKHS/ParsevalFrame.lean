import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Parseval frames in a Hilbert space

A family `{f_i}` in a Hilbert space `E` is a **Parseval frame** if the first Parseval
identity `‖h‖² = ∑ᵢ |⟪f_i, h⟫|²` holds for all `h` — orthonormality and even linear
independence are *not* required.  We prove the standard characterizations:

* the projection of an orthonormal basis of `E` onto a closed subspace `M` is a Parseval
  frame for `M`;
* `{f_i}` is a Parseval frame iff the analysis operator `h ↦ (⟪f_i, h⟫)ᵢ` is a
  well-defined isometry into `ℓ²(ι)`, iff the reconstruction formula
  `h = ∑ᵢ ⟪f_i, h⟫ • f_i` holds;
* the polarized Parseval identity `⟪h₁, h₂⟫ = ∑ᵢ ⟪h₁, f_i⟫ ⟪f_i, h₂⟫`;
* (dilation) every Parseval frame is the compression of an orthonormal basis of a larger
  Hilbert space: there is an isometry `V : E → ℓ²(ι)` with `V* (δ_i) = f_i`.

**Bibliographic comments.** Frames originate with R. J. Duffin and A. C. Schaeffer,
*A class of nonharmonic Fourier series*, Trans. Amer. Math. Soc. **72** (1952), 341–366.
The dilation theorem is due to D. Han and D. R. Larson, *Frames, bases and group
representations*, Mem. Amer. Math. Soc. **147** (2000), no. 697.
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- **Parseval frame**: a family `f : ι → E` such that `‖h‖² = ∑ᵢ |⟪f_i, h⟫|²`
(unordered sum) for every `h ∈ E`. -/
def IsParsevalFrame (f : ι → E) : Prop :=
  ∀ h : E, HasSum (fun i => ‖⟪f i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2)

/-- An orthonormal basis (as a Hilbert basis) is a Parseval frame. -/
theorem HilbertBasis.isParsevalFrame [CompleteSpace E] (e : HilbertBasis ι 𝕜 E) :
    IsParsevalFrame 𝕜 (e : ι → E) := by
  sorry

/-- **Compressions of orthonormal bases are Parseval frames**: the orthogonal projection
of a Hilbert basis of `E` onto a closed subspace `M` is a Parseval frame for `M`. -/
theorem isParsevalFrame_orthogonalProjection [CompleteSpace E]
    (e : HilbertBasis ι 𝕜 E) (M : Submodule 𝕜 E) [CompleteSpace M] :
    IsParsevalFrame 𝕜 fun i => M.orthogonalProjection (e i) := by
  sorry

/-- A Parseval frame is norm-bounded by `1`. -/
theorem IsParsevalFrame.norm_le_one {f : ι → E} (hf : IsParsevalFrame 𝕜 f) (i : ι) :
    ‖f i‖ ≤ 1 := by
  sorry

/-- **Analysis-operator characterization**: `f` is a Parseval frame iff
`h ↦ (⟪f_i, h⟫)ᵢ` is a well-defined linear isometry into `ℓ²(ι)`. -/
theorem isParsevalFrame_iff_exists_isometry {f : ι → E} :
    IsParsevalFrame 𝕜 f
      ↔ ∃ V : E →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2, ∀ h i, V h i = ⟪f i, h⟫_𝕜 := by
  sorry

/-- **Reconstruction formula**: for a Parseval frame, `h = ∑ᵢ ⟪f_i, h⟫ • f_i`
(unordered norm convergence). -/
theorem IsParsevalFrame.hasSum_reconstruction [CompleteSpace E] {f : ι → E}
    (hf : IsParsevalFrame 𝕜 f) (h : E) :
    HasSum (fun i => ⟪f i, h⟫_𝕜 • f i) h := by
  sorry

/-- Conversely, the reconstruction formula for all vectors makes `f` a Parseval frame. -/
theorem isParsevalFrame_of_hasSum_reconstruction [CompleteSpace E] {f : ι → E}
    (hrec : ∀ h : E, HasSum (fun i => ⟪f i, h⟫_𝕜 • f i) h) :
    IsParsevalFrame 𝕜 f := by
  sorry

/-- **Polarized Parseval identity** for a Parseval frame:
`⟪h₁, h₂⟫ = ∑ᵢ ⟪h₁, f_i⟫ · ⟪f_i, h₂⟫`. -/
theorem IsParsevalFrame.hasSum_inner [CompleteSpace E] {f : ι → E}
    (hf : IsParsevalFrame 𝕜 f) (h₁ h₂ : E) :
    HasSum (fun i => ⟪h₁, f i⟫_𝕜 * ⟪f i, h₂⟫_𝕜) ⟪h₁, h₂⟫_𝕜 := by
  sorry

/-- **Dilation (Han–Larson)**: every Parseval frame for `E` is the compression of the
canonical orthonormal basis of `ℓ²(ι)`: there is a linear isometry `V : E → ℓ²(ι)`
whose adjoint maps the canonical basis vectors to the frame vectors. -/
theorem IsParsevalFrame.exists_dilation [CompleteSpace E] [DecidableEq ι] {f : ι → E}
    (hf : IsParsevalFrame 𝕜 f) :
    ∃ V : E →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2,
      ∀ i, V.toContinuousLinearMap.adjoint (lp.single 2 i (1 : 𝕜)) = f i := by
  sorry

end StatLean.NonparametricStatistics
