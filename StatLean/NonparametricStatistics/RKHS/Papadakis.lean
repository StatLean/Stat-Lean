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
open scoped InnerProductSpace ENNReal

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- A Parseval frame of an RKHS expands the kernel pointwise:
`K(x, y) = ∑ᵢ f_i(x) · conj (f_i y)`. -/
theorem IsParsevalFrame.hasSum_scalarKernel {f : ι → H} (hf : IsParsevalFrame 𝕜 f)
    (x y : X) :
    HasSum (fun i => (f i : H) x * conj ((f i : H) y)) (scalarKernel H x y) := by
  have H0 := hf.hasSum_inner (kernelFun H x) (kernelFun H y)
  rw [← scalarKernel_eq_inner] at H0
  simpa [inner_kernelFun, inner_kernelFun_right] using H0

/-! ### Auxiliary material for the converse -/

/-- `⟪h, f i⟫ · ⟪f i, h⟫` is the real scalar `‖⟪f i, h⟫‖²`. -/
private theorem inner_mul_inner_self' (f : ι → H) (h : H) (i : ι) :
    ⟪h, f i⟫_𝕜 * ⟪f i, h⟫_𝕜 = ((‖⟪f i, h⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm (𝕜 := 𝕜) (f i) h, RCLike.mul_conj, RCLike.norm_conj]
  norm_cast

/-- `⟪h, h⟫` is the real scalar `‖h‖²`. -/
private theorem inner_self_ofReal' (h : H) : ⟪h, h⟫_𝕜 = ((‖h‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; ring

/-- The `𝕜`-valued Parseval identity at `h` implies its real form. -/
private theorem hasSum_sq_of_hasSum_inner {f : ι → H} {h : H}
    (H0 : HasSum (fun i => ⟪h, f i⟫_𝕜 * ⟪f i, h⟫_𝕜) ⟪h, h⟫_𝕜) :
    HasSum (fun i => ‖⟪f i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2) := by
  have := H0.mapL (RCLike.reCLM (K := 𝕜))
  simpa only [Function.comp_def, RCLike.reCLM_apply, inner_mul_inner_self', inner_self_ofReal',
    RCLike.ofReal_re] using this

/-- The defining `HasSum` of the `ℓ²` norm, specialized to `p = 2`. -/
private theorem lp2_hasSum_sq' (x : lp (fun _ : ι => 𝕜) 2) :
    HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
  have h2 : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  simpa using lp.hasSum_norm h2 x

/-- The span of the kernel functions `k_x` is dense in a scalar RKHS. -/
private theorem dense_span_kernelFun :
    Dense ((Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)) : Submodule 𝕜 H) :
      Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hle : Submodule.span 𝕜 {y : H | ∃ (x : X) (v : 𝕜), RKHS.kerFun H x v = y}
      ≤ Submodule.span 𝕜 (Set.range (kernelFun (𝕜 := 𝕜) (X := X) H)) := by
    rw [Submodule.span_le]
    rintro y ⟨x, v, rfl⟩
    have hv : RKHS.kerFun H x v = v • kernelFun (𝕜 := 𝕜) H x := by
      change RKHS.kerFun H x v = v • RKHS.kerFun H x 1
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hmono := Submodule.topologicalClosure_mono hle
  rw [RKHS.kerFun_dense] at hmono
  exact top_le_iff.1 hmono

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
