FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-core — scalar RKHS bridge

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/Basic.lean
- StatLean/NonparametricStatistics/RKHS/KernelFunction.lean
- StatLean/NonparametricStatistics/RKHS/OrthonormalExpansion.lean
- StatLean/NonparametricStatistics/RKHS/Subspace.lean
- StatLean/NonparametricStatistics/RKHS/Continuity.lean

Build targets (foreground, in this order as you close files):
`lake build StatLean.NonparametricStatistics.RKHS.Basic` (then KernelFunction,
OrthonormalExpansion, Subspace, Continuity).

Close every `sorry`.  Work in file order — later files use earlier lemmas.

## Proof guidance

The key Mathlib file is `Mathlib/Analysis/InnerProductSpace/Reproducing.lean` — READ IT
FIRST (`.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Reproducing.lean`).
It provides `RKHS.kerFun`, `RKHS.kernel`, `RKHS.kerFun_inner : ⟪kerFun H x v, f⟫ = ⟪v, f x⟫`,
`RKHS.inner_kerFun`, `RKHS.kerFun_dense`, `RKHS.isHermitian_kernel`,
`RKHS.posSemidef_kernel`, `RKHS.posSemidef_tfae`, plus simp lemmas
(`coe_add`, `coe_smul`, `continuous_eval`, …).  Our `kernelFun H x = RKHS.kerFun H x 1`
and `scalarKernel H x y = (kernelFun H y) x`.

- `inner_kernelFun`: `kerFun_inner` with `v = 1`, then `⟪1, z⟫_𝕜 = z` (RCLike inner on
  `𝕜` is `conj a * b`; `RCLike.inner_apply`).
- `scalarKernel_eq_inner`: apply `inner_kernelFun` at `f := kernelFun H y`, point `x`.
- `scalarKernel_eq_kernel_one`: `RKHS.kerFun_apply` gives `kerFun H y v x = kernel H x y v`.
- `scalarKernel_conj_symm`: from `scalarKernel_eq_inner` and `inner_conj_symm`.
- `scalarKernel_self`: `inner_self_eq_norm_sq_to_K` (or `RCLike` variant).
- `evalCLM_eq_innerSL_kernelFun`: `ContinuousLinearMap.ext`, then `innerSL_apply` +
  `inner_kernelFun`.
- `norm_evalCLM`: rewrite via previous, then `innerSL_apply_norm : ‖innerSL 𝕜 x‖ = ‖x‖`.
- `norm_apply_le`: Cauchy–Schwarz `norm_inner_le_norm` through `inner_kernelFun`.
- `tendsto_apply_of_tendsto`: compose `RKHS.continuous_eval` with `h`.
- `IsKernelFun.im_sum_eq_zero`: the Hermitian condition makes the double sum equal its
  own star: reindex `Finset.sum_comm`, use `conj_symm`; a self-conjugate element of `𝕜`
  has `im = 0` (`RCLike.conj_eq_iff_im`).
- `isKernelFun_featureKernel`: the double sum is `⟪∑ i, a i • φ (x i), ∑ j, a j • φ (x j)⟫`
  expanded by `inner_sum`/`sum_inner`/`inner_smul_left/right`; then
  `inner_self_nonneg`.  Mind the order: `conj (a i) * a j * ⟪φ xᵢ, φ xⱼ⟫`.
- `isKernelFun_scalarKernel`: rewrite with `scalarKernel_eq_featureKernel`, apply
  the feature lemma.
- `gramian_posSemidef` / `gramian_posDef_iff_linearIndependent`: `Matrix.PosSemidef`
  over `Fin n` — use `Matrix.posSemidef_iff_...` or unfold: quadratic form is
  `‖∑ i, x i • h i‖²`; PosDef iff no nontrivial combination vanishes
  (`linearIndependent_iff'` for Fin-indexed families; `Fintype.linearIndependent_iff`).
- `hasSum_kernelFun` (Thm 2.4): `e.hasSum_repr (kernelFun H y)` gives
  `HasSum (fun i => e.repr (k_y) i • e i) k_y`; `HilbertBasis.repr_apply_apply` or
  `repr_self`… the coefficient is `⟪e i, k_y⟫ = conj ((e i) y)` via `inner_kernelFun` +
  `inner_conj_symm`.
- `hasSum_scalarKernel`: apply the continuous linear evaluation `evalCLM 𝕜 H x` to the
  previous `HasSum` (`HasSum.mapL` or `ContinuousLinearMap.hasSum`).
- `hasSum_scalarKernel_self`: from `hasSum_scalarKernel` at `y = x`; each term
  `conj((e i) x) * (e i) x` has `re = ‖(e i) x‖²`(`RCLike.conj_mul` / `normSq`);
  use `HasSum.mapL reCLM` (`RCLike.reCLM`).
- `Subspace.lean`: the coercion of `H₀.subtypeL` is the subtype inclusion, so
  `coeCLM_injective` reduces to injectivity of `coeCLM` and `Subtype.val_injective`.
  `kernelFun_submodule`: characterize `k_x^{H₀}` by the reproducing property tested
  against members of `H₀`; both sides have equal inner products against every `f ∈ H₀`
  (`Submodule.starProjection_inner_eq_right`-style lemmas; search
  `starProjection` API in `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`),
  then use that two elements of `H₀` with equal inner products against all of `H₀`
  coincide (`ext_inner_right` on the subtype).
- `Continuity.lean`: `norm_kernelFun_sub_sq` by expanding
  `‖a − b‖² = re(⟪a,a⟫ − ⟪a,b⟫ − ⟪b,a⟫ + ⟪b,b⟫)` (`norm_sub_sq` or
  `inner_sub_sub_self`) and rewriting each inner product as a kernel value via
  `scalarKernel_eq_inner`.  `continuous_kernelFun`: continuity from
  `tendsto_iff_norm_sub_tendsto_zero`-style: the square of the distance tends to 0
  since `K` is continuous at `(y₀,y₀)`; assemble with
  `Continuous.comp`/`continuous_iff_continuousAt` and `Real.sqrt` continuity, or
  directly `(continuous_iff_continuousAt).2` + squeeze.  Then
  `continuous_coe_of_continuous_scalarKernel`: `|f y − f y₀| ≤ ‖f‖·‖k_y − k_{y₀}‖`
  via `inner_kernelFun` + Cauchy–Schwarz, compose with `continuous_kernelFun`.
