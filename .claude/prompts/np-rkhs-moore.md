FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-moore — Moore's theorem, uniqueness, rank-one, inner kernel

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/Moore.lean
- StatLean/NonparametricStatistics/RKHS/Uniqueness.lean
- StatLean/NonparametricStatistics/RKHS/RankOne.lean
- StatLean/NonparametricStatistics/RKHS/InnerKernel.lean

Build targets: `lake build StatLean.NonparametricStatistics.RKHS.Moore` (then
Uniqueness, RankOne, InnerKernel — independent of each other, all depend on the
already-green Basic/KernelFunction).

Close every `sorry`.  Statements are frozen (see header rule 5).

## Proof guidance — Moore.lean

Read `Mathlib/Analysis/InnerProductSpace/Reproducing.lean` first: `RKHS.posSemidef_tfae`
is the workhorse — for `K : Matrix X X (V →L[𝕜] V)`,
`K.PosSemidef ↔ K.IsHermitian ∧ ∀ vv : X →₀ V, 0 ≤ re (vv.sum fun x w => vv.sum fun x' w' => ⟪K x' x w, w'⟫)`.
With `V = 𝕜`: `⟪(K' x' x) w, w'⟫_𝕜 = conj (K x' x * w) * w'`.

- `toCLMMatrix_apply`: `smul` of the identity CLM: `(c • 1) v = c * v` — `simp`.
- `isKernelFun_iff_posSemidef_toCLMMatrix`: use `posSemidef_tfae.out 0 2`.  Bridge
  Finsupp double sums over `X →₀ 𝕜` to our `Fin n` double sums: given a Finsupp `vv`,
  enumerate its support (`vv.support.toList` or `Finsupp.sum` over `Finset` →
  `Fintype` of the support → equiv with `Fin n`); conversely, given `x : Fin n → X`
  and `a : Fin n → 𝕜` build `∑ i, Finsupp.single (x i) (a i)` — beware repeated points:
  `Finsupp.single`-sums merge coefficients, which is exactly why the two quadratic
  forms agree (`Finsupp.sum_sum_index`, `Finsupp.sum_single_index`).  Also the
  Hermitian sides match by definition (`Matrix.IsHermitian`, `Matrix.ext_iff`,
  `ContinuousLinearMap.adjoint` of scalar multiplication is conj-multiplication:
  `star (c • 1) = conj c • 1` — search `ContinuousLinearMap.star_smul`,
  `adjoint_smul`, `adjoint_id`).  This bridge is the main work of the lane; take it
  slowly, one direction per commit.
- `scalarKernel_ofScalarKernel`: from `RKHS.kernel_ofKernel : kernel (OfKernel K') = K'`
  and `scalarKernel_eq_kernel_one` (Basic.lean) + `toCLMMatrix_apply`.
- `IsKernelFun.exists_rkhs`: package `OfScalarKernel` with
  `haveI : Fact (IsKernelFun K) := ⟨hK⟩`.

## Proof guidance — Uniqueness.lean (Prop 2.3)

- Strategy: build the equivalence on spans of kernel functions.  Define the linear map
  sending `k_x^{H₁} ↦ k_x^{H₂}`.  Cleanest formal route: both `H₁` and `H₂` receive an
  isometry from the *same* Moore space `OfScalarKernel (scalarKernel H₁)`… but a
  direct construction is fine: on `W₁ := span {k_x^{H₁}}`, the map
  `∑ αⱼ k_{xⱼ}^{H₁} ↦ ∑ αⱼ k_{xⱼ}^{H₂}` is well-defined AND isometric simultaneously
  because `‖∑ αⱼ k_{xⱼ}^{Hᵢ}‖²` is the same kernel double sum in both spaces
  (equal kernels): if a combination vanishes in `H₁` its image has norm 0 in `H₂`.
  Formalize via the "isometric on a dense subspace extends" pattern:
  `LinearIsometry` on the span (or a `LinearMap` with `‖T f‖ = ‖f‖` on the span),
  extend to the closure = ⊤ (`RKHS.kerFun_dense`; note our scalar kernel functions
  span the same closure as Mathlib's `kerFun` image — with `V = 𝕜`,
  `kerFun H x v = v • kernelFun H x`, so the two spans coincide:
  prove `kerFun H x v = v • RKHS.kerFun H x 1` by `map_smul`-style
  `(kerFun H x).map_smul` + `mul_one`, i.e. `v = v • (1:𝕜)`).
  For the extension: `LinearIsometry` from a dense subspace —
  search `DenseInducing.extend`, or use `Completion`-free route:
  define `T₀ : W₁ →ₗᵢ H₂`, extend via `T₀.extend`?  If no off-the-shelf extension
  lemma fits, do it by hand with `IsUniformInducing`/`DenseRange` +
  `Isometry.completion`-style arguments, or use `ContinuousLinearMap.extend` (exists
  for dense range + uniform continuity) and then upgrade to `≃ₗᵢ` via symmetry
  (construct the inverse the same way from `H₂` to `H₁`, and check both compositions
  are the identity on the dense spans → everywhere by continuity).
  Evaluation-commuting: on spans it is the kernel identity; extend by continuity of
  evaluation (`RKHS.continuous_eval`).
- `evaluation_commuting_unique`: two maps agreeing pointwise on values: for each `f`,
  `(e₁ f) x = (e₂ f) x` for all `x` ⇒ `e₁ f = e₂ f` by `RKHS.ext` (DFunLike.ext).
- `range_coe_eq_of_scalarKernel_eq`: from the equivalence, both inclusions.

## Proof guidance — RankOne.lean (Prop 2.19)

- `isKernelFun_rankOne`: quadratic form is `‖∑ conj(aᵢ) f₀(xᵢ)‖²`-shaped:
  `∑ᵢⱼ conj aᵢ aⱼ f₀(xᵢ) conj (f₀ (xⱼ)) = (∑ᵢ conj aᵢ f₀ xᵢ) * conj (∑ⱼ conj aⱼ f₀ xⱼ)`
  — check the algebra carefully, it is `z * conj z = ‖z‖²` up to arrangement
  (`RCLike.mul_conj`); Hermitian part: `map_mul`, `conj_conj`.
- `exists_unit_spanning_of_scalarKernel_rankOne`: pick `y₀` with `f₀ y₀ ≠ 0`
  (`Function.ne_iff`).  Set `g := (conj (f₀ y₀))⁻¹ • kernelFun H y₀`.  Compute
  `g x = (conj (f₀ y₀))⁻¹ * K(x, y₀) = f₀ x` — wait: `K(x,y₀) = f₀ x * conj (f₀ y₀)`
  so `g x = f₀ x` ✓.  Norm: `‖k_{y₀}‖² = K(y₀,y₀) = ‖f₀ y₀‖²` ⇒ `‖g‖ = 1`.
  Spanning: every `k_y = conj (f₀ y) • g` (check values:
  both sides evaluate to `f₀ · conj (f₀ y)`… but equality in `H` needs more than equal
  values — no! members of an RKHS are DETERMINED by their values:
  `RKHS.ext`/`coeCLM_injective`.  Use that).  Then every `h ∈ H`: `h` is a norm-limit
  of span of `{k_y} ⊆ 𝕜 ∙ g`, and `𝕜 ∙ g` is closed (finite-dim) ⇒ `h ∈ 𝕜 ∙ g`
  (`Submodule.isClosed_of_finiteDimensional`, density from `kerFun_dense` — as in the
  Moore lane, scalar kernel functions and `kerFun` have the same span).
- `kernelFun_of_scalarKernel_rankOne`: `RKHS.ext`: both sides have values
  `x ↦ f₀ x * conj (f₀ y)`… again NO — `conj (f₀ y) • g` has values
  `conj (f₀ y) * f₀ x` ✓ equal; and `kernelFun H y` has values `K(x,y)` ✓.

## Proof guidance — InnerKernel.lean (Prop 2.24)

- `dualRKHS` injectivity: `⟪v, w⟫ = 0` for all `v` (take `v = w`) ⇒ `w = 0`
  (`inner_self_eq_zero`).
- `dualRKHS_kernelFun`: characterize by the reproducing property: for all `w`,
  `⟪kernelFun L x, w⟫ = (w : L → 𝕜) x = ⟪x, w⟫` (definition of coeCLM), so
  `kernelFun L x = x` by `ext_inner_right`.  Mind: `inner_kernelFun` from Basic gives
  the first equality; unfold the `letI`.
- `dualRKHS_scalarKernel`: `scalarKernel x y = (kernelFun y) x = coeCLM (y) x = ⟪x, y⟫`
  after the previous lemma.
- `isKernelFun_inner`: `isKernelFun_featureKernel` with `φ = id`.
- `dualRKHS_range_coe`: `⊆`: `w ↦ innerSL 𝕜 · w`-shaped functionals are CLMs
  (`innerSL`-flip; exhibit `T := (innerSL 𝕜).flip w`?  check: want `T v = ⟪v, w⟫`;
  `innerSL 𝕜 v w = ⟪v,w⟫`, so `T = fun v => innerSL 𝕜 v w` — package via
  `(innerSL 𝕜).flip w`… verify flip's argument order with `rfl`/`simp`).
  `⊇`: Riesz — `InnerProductSpace.toDual` is surjective
  (`Mathlib/Analysis/InnerProductSpace/Dual.lean`:
  `InnerProductSpace.toDual : E ≃ₗᵢ⋆[𝕜] (E →L[𝕜] 𝕜)`, `toDual_apply : toDual x y = ⟪x, y⟫`);
  for `T : L →L 𝕜` take `w := toDual.symm T`, then
  `(w : L → 𝕜) = fun v => ⟪v, w⟫ = T` by `toDual_apply` + `symm_apply`.
