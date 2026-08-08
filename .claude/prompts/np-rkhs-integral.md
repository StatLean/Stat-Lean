FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-integral — integral operators, range spaces, Mercer defs, operator lemmas

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/IntegralOperator.lean
- StatLean/NonparametricStatistics/RKHS/RangeSpace.lean
- StatLean/NonparametricStatistics/RKHS/Mercer/Defs.lean
- StatLean/NonparametricStatistics/RKHS/Mercer/OperatorLemmas.lean

Build targets: `lake build StatLean.NonparametricStatistics.RKHS.IntegralOperator`
(then RangeSpace, Mercer.Defs, Mercer.OperatorLemmas).

Close every `sorry` (including the `map_add'`/`map_smul'`/bound sorries inside the
definition `mercerCLM`).  Statements are frozen (see header rule 5).

## IntegralOperator.lean

- `IsL2Symbol.conj`: `MemLp` of the conjugate — search `MemLp.star` /
  `RCLike.memLp_conj` / `MemLp.congr'`… fallback: `MemLp` is `AEStronglyMeasurable ∧
  eLpNorm < ∞`; conj preserves both (`AEStronglyMeasurable.star`?
  `RCLike.continuous_conj.comp_aestronglyMeasurable`, and `eLpNorm` is
  norm-determined: `eLpNorm_congr_norm_ae` with `‖conj z‖ = ‖z‖` — search
  `eLpNorm_norm`, `MemLp.of_le`).
- `integralOp_eq_inner`: `L2.inner_def` (`Mathlib/MeasureTheory/Function/L2Space.lean`)
  gives `⟪a, g⟫ = ∫ conj (a y) * g y`; here `a = (hS.conj x).toLp` whose coeFn is a.e.
  `conj (S x ·)` (`MemLp.coeFn_toLp`), so the integrand is a.e. `S x y * g y`
  (`integral_congr_ae`).  Mind: `⟪a, g⟫_𝕜` in Mathlib's L2 is
  `∫ ⟪a y, g y⟫ = ∫ conj (a y) * g y` for `𝕜`-valued — check `RCLike.inner_apply`
  orientation (CLAUDE.md §7.2).
- `norm_integralOp_le`: rewrite via `integralOp_eq_inner`, then
  `norm_inner_le_norm` (Cauchy–Schwarz).
- `boxProd_symbolAdjoint_eq_featureKernel`: pointwise: `funext x z`;
  `featureKernel 𝕜 φ x z = ⟪φ x, φ z⟫` with `φ = symbolConjLp μ S hS`;
  `L2.inner_def` + coeFn lemmas turn it into
  `∫ conj (conj (S x y)) * conj (S z y) = ∫ S x y * conj (S z y)`
  `= ∫ S x y * symbolAdjoint S y z` ✓ (`conj_conj`, `integral_congr_ae`).
- `isKernelFun_boxProd_symbolAdjoint`: rewrite with the previous +
  `isKernelFun_featureKernel`.

## RangeSpace.lean

- `rangeSpaceRKHS` injectivity: `g` in the closed span of `{symbolConjLp x}` with
  `⟪symbolConjLp x, g⟫ = 0` for all `x` ⇒ `g ⊥ span ⇒ g ⊥ closure ⇒ g ⊥ g ⇒ g = 0`.
  (`Submodule.inner_right_of_mem_orthogonal`-style +
  `Submodule.topologicalClosure`… useful: `mem_orthogonal_span_range_iff`? build by
  hand: orthogonality to generators extends to span (`Submodule.span_induction`) and to
  its closure by continuity of the inner product
  (`Submodule.orthogonal` is closed: `Submodule.isClosed_orthogonal`; simplest:
  `(span …)ᗮ = (span …).topologicalClosureᗮ` — search
  `Submodule.topologicalClosure_orthogonal` / `orthogonal_topologicalClosure`? there is
  `Submodule.orthogonal_eq_orthogonal_topologicalClosure`-like lemma; or use
  `Dense.eq_zero_of_inner_left`-style: `UniformSpace.Completion`-free
  `denseRange_coe.eq_zero_of_inner…` does not apply — do the span_induction route).
- `rangeSpace_apply`: unfold the instance: `f x = ⟪symbolConjLp x, (f : Lp)⟫` is
  definitional (`rfl`-adjacent; if not `rfl`, unfold `coeCLM`/`ContinuousLinearMap.pi`
  applications with `simp [rangeSpaceRKHS]`), then `integralOp_eq_inner` backwards.
- `rangeSpace_kernelFun`: characterize via reproducing: for `f` in the carrier,
  `⟪k_x, f⟫ = f x = ⟪symbolConjLp x, f⟫`; `symbolConjLp x` lies in the carrier
  (`Submodule.subset_span` + `Submodule.le_topologicalClosure` chain +
  `Set.mem_range_self`), and two carrier elements with equal inner products against ALL
  carrier elements are equal (`ext_inner_right` on the subtype; also note inner products
  against `Lp`-elements orthogonal to the carrier vanish for both).  Take care: the
  subtype inner product is inherited (`Submodule.coe_inner`).
- `rangeSpace_scalarKernel`: `K(x,z) = (k_z) x = ⟪symbolConjLp x, symbolConjLp z⟫`
  = `featureKernel … x z` = `boxProd …` (IntegralOperator lemma).
- `range_integralOp_eq_range_coe`: `⊇` is `rangeSpace_apply`.  `⊆`: decompose
  `g = g₀ + g₁` with `g₀` in the carrier `V` and `g₁ ∈ Vᗮ`
  (`Submodule.starProjection` exists: the carrier is complete — instance in file);
  `integralOp μ S g₁ = 0` pointwise (each `symbolConjLp x ∈ V`), so
  `integralOp μ S g = integralOp μ S g₀` (`map_add`-style linearity of `integralOp` in
  `g`: prove a `private` lemma `integralOp_add`/`integralOp_smul` from
  `integral_add`… or via `integralOp_eq_inner` + `inner_add_right`).
- `rangeSpace_norm_eq_sInf`: the preimages of `⇑f` under `integralOp` are exactly
  `{(f : Lp) + w : w ∈ Vᗮ}` (injectivity on V + the kernel computation above), with
  norms `‖f‖² + ‖w‖²` (Pythagoras `norm_add_sq` + orthogonality), minimized at `w = 0`;
  conclude `sInf (norm '' …) = ‖f‖` (`csInf` API: `le_csInf` + `csInf_le` with
  `Set.mem_image`; boundedness below by 0).
- `rangeSpace_norm_attained`: contained in the previous computation (`w = 0` member).

## Mercer/Defs.lean

- `isL2Symbol_of_continuous`: sections are continuous
  (`Continuous.comp` of `hKc` with `Continuous.prodMk_left`-style:
  `hKc.comp (Continuous.prodMk_right x)`… search `Continuous.along` — concretely
  `fun y => K x y = (fun p => K p.1 p.2) ∘ (fun y => (x, y))`), continuous functions on
  a compact space with finite measure are in every `Lp`:
  search `Continuous.memLp_of_isCompact...` / `MemLp.of_bound` with the sup bound
  (`IsCompact.exists_bound_of_continuousOn` or `Continuous.bounded_above_of_compactSpace`;
  cleanest: `Continuous.memLp` exists? try `_root_.Continuous.memLp` — otherwise
  `memLp_of_bounded` route: `MemLp.of_bound (aestronglyMeasurable) C h`).
- `memLp_integralOp_of_continuous`: `integralOp μ K g` is continuous (prove the
  Mercer/Basic-style estimate directly here or bound):
  `‖integralOp μ K g x‖ ≤ ‖symbolConjLp x‖ ‖g‖ ≤ C` uniformly (sup of `‖K‖` on the
  compact square × `√μ(X)`), and it is measurable — easiest: prove continuity
  (uniform continuity of `K` on the compact square:
  `CompactSpace.uniformContinuous_of_continuous`; then
  `|T g x − T g z| ≤ ‖K(x,·) − K(z,·)‖_{L²} ‖g‖` and the L² difference is small —
  this is Prop 11.9's argument; it lives here because the definition needs it), then
  `Continuous.memLp`-style as above.  You may add `private` lemmas.
- `mercerCLM` fields: `map_add'`/`map_smul'`: `Lp.ext`-style a.e. equality:
  `coeFn_toLp` + linearity of the integral (`integral_add`, `integral_smul` — with
  integrability from Cauchy–Schwarz: `MemLp.integrable_mul` for L²×L², see CLAUDE.md
  §7.4).  Bound: `‖T g‖_{L²} ≤ √(μ(univ)) · C · ‖g‖` from the uniform pointwise bound
  (`eLpNorm_le_of_ae_bound`, then `Lp.norm_toLp`… search `MemLp.toLp` norm lemmas
  `norm_toLp`, `eLpNorm_congr_ae`).
- `mercerCLM_coeFn_ae`: `MemLp.coeFn_toLp` + unfolding `mkContinuousOfExistsBound`
  (`LinearMap.mkContinuousOfExistsBound_apply` — it should be `rfl`-adjacent).
- `inner_mercerCLM`: `L2.inner_def` + `integral_congr_ae` with `mercerCLM_coeFn_ae`.

## Mercer/OperatorLemmas.lean

- `inner_map_eq_zero_of_norm_attaining`: WLOG `‖k‖ ≤ 1`-free: follow the book:
  reduce to real/imaginary parts.  Over `𝕜`, first multiply `k` by a unimodular scalar
  so that `⟪A h, A k⟫ ≥ 0` (real and nonneg) — take `c := conj (⟪A h, A k⟫)/‖⟪A h, A k⟫‖`
  when nonzero.  Also normalize `k` to a unit vector (case `k = 0` trivial).  Then for
  real `t`, `u t := Real.cos t • h + Real.sin t • k` is a unit vector
  (`⟪h,k⟫ = 0`, `norm_add_sq`…: `‖u t‖² = cos² + sin² = 1`), so
  `g t := ‖A (u t)‖²  ≤ ‖A‖²` with `g 0 = ‖A‖²`.  Expand
  `g t = cos²t ‖Ah‖² + 2 cos t sin t · re ⟪Ah, Ak⟫ + sin²t ‖Ak‖²`; then
  `g'(0) = 2 re ⟪Ah, Ak⟫`, and `t = 0` being a max forces it `= 0`
  (`IsLocalMax`… or avoid calculus: from
  `g t ≤ g 0` for all `t` derive the linear-in-`t` term must vanish by taking `t → 0±`:
  `cos²t ‖Ah‖² ≤ ‖Ah‖²` gives
  `2 cos t sin t re⟪⟫ ≤ (1 − cos²t)(‖A‖² ) − sin²t ‖Ak‖² ≤ sin²t (‖A‖²)`, divide by
  `sin t` for small `t > 0` and let `t → 0`, similarly `t < 0` — or pick the slick
  algebraic route: for all real `s`,
  `‖A (h + s•k)‖² ≤ ‖A‖² ‖h + s•k‖² = ‖A‖² (1 + s²)`, expand LHS
  `= ‖Ah‖² + 2 s re⟪Ah, Ak⟫ + s² ‖Ak‖²`, so
  `2 s re⟪Ah,Ak⟫ ≤ s² (‖A‖² − ‖Ak‖²) + (‖A‖² − ‖Ah‖²)· 1`… with `‖Ah‖ = ‖A‖`:
  `2 s re⟪Ah,Ak⟫ ≤ s² ‖A‖²`; `nlinarith`-able for all `s` ⇒ `re⟪Ah,Ak⟫ = 0`
  (take `s = ±ε`; `le_of_forall_lt_iff…` or pick `s := re⟪Ah,Ak⟫ / ‖A‖²` cleverly).
  This inequality route avoids derivatives entirely — RECOMMENDED.  Then repeat with
  `i•k`-twist (or the initial phase normalization) to kill the imaginary part.
- `isEigenvector_of_norm_attaining`: write `P h = c • h + k`, `c := ⟪h, P h⟫`,
  `k := P h − c•h ⊥ h`.  `re c ≥ 0` from positivity
  (`ContinuousLinearMap.IsPositive` API: `IsPositive.inner_nonneg`-shaped —
  in Mathlib: `hP.2` is `0 ≤ re ⟪T x, x⟫`-style `reApplyInnerSelf`; also
  `IsPositive.isSelfAdjoint` gives `⟪h, Ph⟫` real).  Apply the previous lemma with
  `A := P` and this `k`: `0 = ⟪P h, P k⟫`.  Also `P` self-adjoint:
  `0 = ⟪P k, P h⟫ = ⟪P k, c•h + k⟫ = c ⟪Pk, h⟫?…` follow the book computation:
  `0 ≤ ⟪P k, k⟫`, and `⟪P k, k⟫ = −conj c… ` do the algebra with
  `hP.isSelfAdjoint` rewrites; conclude `k = 0` (or `‖P‖ = 0` degenerate case) and
  `c = ‖P‖` from `‖P h‖ = ‖P‖` (`‖Ph‖² = ‖c‖²`… with `k = 0`, `‖c‖ = ‖P‖` and `c`
  real nonneg ⇒ `c = ‖P‖`).

## Note on `rangeSpaceKernelFun` / `rangeSpaceScalarKernel`

These wrappers (in RangeSpace.lean) pass the carrier's `CompleteSpace` instance
explicitly (`rangeSpaceCompleteSpace`) because bare TC synthesis records a different
(defeq but not instance-transparent) uniformity than `kernelFun`'s slot expects.  They
are definitionally `kernelFun (rangeSpaceCarrier μ S hS) x` etc.; unfold them and use
the generic `RKHS/Basic.lean` lemmas with the explicit instance.
