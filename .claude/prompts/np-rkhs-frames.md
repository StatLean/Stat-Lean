FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-frames — Parseval frames + Papadakis

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/ParsevalFrame.lean
- StatLean/NonparametricStatistics/RKHS/Papadakis.lean

Build targets: `lake build StatLean.NonparametricStatistics.RKHS.ParsevalFrame` then
`lake build StatLean.NonparametricStatistics.RKHS.Papadakis`.

Close every `sorry`.  Statements are frozen (see header rule 5).

## Proof guidance

Key Mathlib: `Mathlib/Analysis/InnerProductSpace/l2Space.lean` (`HilbertBasis`,
`lp`, `lp.single`, `HilbertBasis.hasSum_repr`, `HilbertBasis.repr_apply_apply`,
`lp.hasSum_single`…), `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`.

- `HilbertBasis.isParsevalFrame`: Parseval identity — `e.hasSum_inner_mul_inner` or
  `‖h‖² = ‖e.repr h‖²` with `lp.norm_eq...`; simplest: `e.hasSum_inner_mul_inner h h`
  variants; note `⟪e i, h⟫ = e.repr h i`, and `HasSum (fun i => ‖e.repr h i‖ ^ 2) (‖h‖ ^ 2)`
  should be derivable from the isometry `e.repr` (`lp.hasSum_norm...` /
  `MemLp`-style lemmas for `lp 2`).  Search `hasSum` in l2Space.lean.
- `isParsevalFrame_orthogonalProjection` (Prop 2.7): for `h ∈ M`,
  `⟪P(e i), h⟫_M = ⟪e i, h⟫_E` (adjoint/`starProjection` identities:
  `Submodule.orthogonalProjection` is self-adjoint on its range; concretely
  `⟪(M.orthogonalProjection (e i) : E), h⟫ = ⟪e i, h⟫` for `h ∈ M` by
  `Submodule.inner_starProjection_left_eq_right`-style lemmas — search
  `starProjection` / `orthogonalProjection_inner_eq` in Projection/Basic.lean).
  Then reuse the Hilbert-basis Parseval identity.
- `IsParsevalFrame.norm_le_one`: test the frame identity at `h := f i`; one term of the
  nonnegative sum is `‖⟪f i, f i⟫‖² = ‖f i‖⁴ ≤ ‖f i‖²` ⇒ `‖f i‖ ≤ 1` (case `f i = 0`
  separately; `le_hasSum` picks out one term).
- `isParsevalFrame_iff_exists_isometry` (Prop 2.8, 1⇔2): forward — define
  `V : E →ₗᵢ lp` via `LinearIsometry.mk`: the map `h ↦ (fun i => ⟪f i, h⟫)` lands in
  `lp 2` because the frame identity gives `Memℓp` (`memℓp_gen` with the `HasSum` of
  squares); norm preservation is the identity itself (`lp.norm_eq_tsum...` for `p = 2`;
  search `lp.norm_rpow_eq_tsum` / `lp.norm_sq_eq_inner`).  Backward: `‖V h‖² = ‖h‖²`
  unfolds to the required `HasSum` (the `lp` norm-sum equivalence again).
- `IsParsevalFrame.hasSum_reconstruction` (Prop 2.8, 1⇒3): with the isometry `V`:
  `V.toContinuousLinearMap.adjoint (lp.single 2 i 1) = f i` (compute
  `⟪h, V* (single i 1)⟫ = ⟪V h, single i 1⟫ = conj (⟪f i, h⟫)`… careful with
  conjugates; then `V* V = 1` (isometry: `LinearIsometry.adjoint_comp_self`-like —
  or prove `⟪V* V h, h'⟫ = ⟪h, h'⟫` directly) and push `V h = ∑ single` through `V*`
  (`lp.hasSum_single` + continuity of `V*`).
- `isParsevalFrame_of_hasSum_reconstruction` (3⇒1): `⟪h, h⟫ = ∑ ⟪h, f i⟫⟪f i, h⟫` by
  applying `inner h ·` (continuous) to the reconstruction `HasSum`; each term
  `⟪h, f i⟫ ⟪f i, h⟫ = ‖⟪f i, h⟫‖²` (`inner_conj_symm`, `RCLike.mul_conj`), then take
  `re`.
- `IsParsevalFrame.hasSum_inner`: polarization — apply `inner h₁ ·` to the
  reconstruction of `h₂`.
- `IsParsevalFrame.exists_dilation` (Prop 2.9): take the isometry `V` from Prop 2.8;
  the adjoint identity `V* (single i 1) = f i` is the computation above.
- `Papadakis.lean` forward: `K(x,y) = ⟪k_x, k_y⟫` (`scalarKernel_eq_inner`), then
  `IsParsevalFrame.hasSum_inner` with `h₁ := kernelFun H x`, `h₂ := kernelFun H y`;
  each term `⟪k_x, f i⟫⟪f i, k_y⟫ = (f i x) * conj (f i y)` by `inner_kernelFun` /
  `inner_kernelFun_right` (in `RKHS/Basic.lean`).
- Papadakis converse: show the analysis map is isometric on the dense span of kernel
  functions.  For `h = ∑ⱼ αⱼ k_{yⱼ}` (finite), expand `‖h‖²` through the kernel and the
  hypothesis into `∑_i ‖⟪f i, h⟫‖²` (all sums finite or `HasSum` in `i`); conclude the
  frame identity for such `h`; extend to all of `H` by density
  (`RKHS.kerFun_dense`) — for the limit argument note both `h ↦ ‖h‖²` and
  `h ↦ ∑ᵢ ‖⟪f i, h⟫‖²` (as a `⨆` of partial sums / via the isometry on the closure)
  behave continuously; a clean route: define the isometry on the span-submodule, extend
  by `DenseInducing`/`LinearIsometry` extension (`LinearIsometry.extend`? search
  `DenseRange` + isometry extension: `Isometry.extend`… or
  `ContinuousLinearMap.extend` of the analysis operator with norm control), then read
  the frame identity back from the extended isometry (`isParsevalFrame_iff_exists_isometry`).
  This is the hardest lemma of the lane; the iff wrapper afterwards is trivial.
