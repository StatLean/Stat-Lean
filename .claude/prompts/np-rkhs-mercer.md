FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-mercer — Mercer basics, compactness, Mercer's theorem, square root

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/Mercer/Basic.lean
- StatLean/NonparametricStatistics/RKHS/Mercer/Compact.lean
- StatLean/NonparametricStatistics/RKHS/Mercer/Theorem.lean
- StatLean/NonparametricStatistics/RKHS/Mercer/SquareRoot.lean

Build targets: `lake build StatLean.NonparametricStatistics.RKHS.Mercer.Basic` (then
Compact, Theorem, SquareRoot).

This is the hardest lane of the batch — DO NOT rush.  Prioritize in this order:
(1) Basic.lean fully; (2) Compact.lean; (3) Theorem.lean `exists_mercerEigensystem`;
(4) kernel-expansion theorems; (5) SquareRoot.lean.  Close every `sorry` you can;
commit after EVERY lemma; leave clearly-documented `sorry`s (comment above with the
missing ingredient) rather than broken proofs.  You may add `private` helper lemmas
in your own files.  Statements are frozen (see header rule 5).

Upstream lemmas you may rely on (already stated, possibly still `sorry`d — that is
fine, import and use them): `norm_apply_le`, `scalarKernel_eq_inner`,
`hasSum_scalarKernel`, `hasSum_scalarKernel_self` (OrthonormalExpansion),
`continuous_kernelFun`, `continuous_coe_of_continuous_scalarKernel` (Continuity),
`integralOp_eq_inner`, `norm_integralOp_le`, `boxProd_symbolAdjoint_eq_featureKernel`
(IntegralOperator), `mercerCLM_coeFn_ae`, `inner_mercerCLM`,
`memLp_integralOp_of_continuous`, `isL2Symbol_of_continuous` (Mercer/Defs),
`inner_map_eq_zero_of_norm_attaining`, `isEigenvector_of_norm_attaining`
(Mercer/OperatorLemmas), `rangeSpace_*` (RangeSpace).

## Mercer/Basic.lean

- `norm_apply_le_sSup`: `norm_apply_le` + `‖k_x‖² = re K(x,x) ≤ ⨆ t, re K(t,t)`
  (the sup exists: continuity on compact ⇒ `BddAbove` via
  `IsCompact.bddAbove_image`; `le_ciSup`).
- `integral_normSq_le`: pointwise bound + `integral_mono` on the constant
  (`integral_const`, measure `μ univ`; integrability of `‖f x‖²`: `f` continuous
  (`continuous_coe_of_continuous_scalarKernel`) ⇒ continuous integrand ⇒ integrable).
- `separableSpace_of_mercer`: `X` compact metric ⇒ separable
  (`TopologicalSpace.SeparableSpace X` instance exists); take countable dense `D ⊆ X`;
  span of `{kernelFun H x : x ∈ D}` is dense in the span of all kernel functions
  (continuity of `x ↦ k_x` = `continuous_kernelFun`), which is dense
  (`RKHS.kerFun_dense` — note `kerFun H x v = v • kernelFun H x`, so equal spans).
  Then a countable dense set: rational/`𝕜`-countable combinations… simpler:
  `TopologicalSpace.separableSpace_of_denseRange`?  Useful Mathlib:
  a topological vector space with a countable set whose span is dense is separable —
  search `Submodule.topologicalClosure`, `TopologicalSpace.SeparableSpace` +
  `DenseRange`, `IsSeparable.span`?  (`Mathlib/Topology/Bases…`,
  `Analysis/Normed/Module/Separable`? — `Submodule.span` of a separable set has
  separable closure: search `IsSeparable`.)
- `tendstoUniformly_diag` (Dini): partial sums `F s x := ∑_{i∈s} ‖eᵢ x‖²` are
  continuous (each `eᵢ` continuous via
  `continuous_coe_of_continuous_scalarKernel`), monotone in `s` (adding nonneg terms;
  `Monotone` w.r.t. `Finset ι` ⊆-order: `Finset.sum_le_sum_of_subset_of_nonneg`),
  converge pointwise to the continuous limit `re K(x,x)`
  (`hasSum_scalarKernel_self` + `HasSum.tendsto_sum_finset`… note
  `HasSum f a ↔ Tendsto (fun s => ∑ i in s, f i) atTop (𝓝 a)` is the definition),
  so `Monotone.tendstoUniformly_of_forall_tendsto`
  (`Mathlib/Topology/UniformSpace/Dini.lean`; `[CompactSpace X]` version) applies.
- `sq_norm_sum_le`: `inner_mul_le_norm_mul_norm` (finite-dim Cauchy–Schwarz) on
  `EuclideanSpace`-free finite sums: interpret the sum as an inner product in
  `s → 𝕜`… simplest: `Finset.inner_mul_le_norm_mul_norm` (search) or directly
  `Finset.sum_mul_sq_le_sq_mul_sq` (the classical finite Cauchy–Schwarz in Mathlib —
  that name exists) with values `‖eᵢ x‖`, `‖eᵢ y‖` after bounding
  `‖∑ conj(eᵢ y) eᵢ x‖ ≤ ∑ ‖eᵢ x‖ ‖eᵢ y‖` (`norm_sum_le` + `norm_mul`).
- `tendstoUniformly_scalarKernel`: uniform Cauchy from the diagonal Dini +
  `sq_norm_sum_le` applied to DIFFERENCES of partial sums (tail sums over
  `s \ t`), then `TendstoUniformly` via `TendstoUniformlyOn.of_uniformCauchy`…
  (`UniformCauchySeqOn` + pointwise limit `hasSum_scalarKernel` ⇒ uniform limit:
  search `TendstoUniformly` `uniformCauchySeqOn_iff_tendstoUniformly`?  Route:
  `tendstoUniformly_iff` ε-form and estimate tails through the diagonal, using that
  diagonal tails are uniformly small by Dini + compactness (two-point sup:
  bound `|∑_{i∉s} conj(eᵢ y) eᵢ x| ≤ √(tail x) √(tail y) ≤ max tails`).
- `norm_mercerCLM_le`: `ContinuousLinearMap.opNorm_le_bound`; pointwise
  Cauchy–Schwarz `‖T g x‖ ≤ ‖K(x,·)‖₂ ‖g‖` (`norm_integralOp_le`), square + integrate
  (`Lp.norm_def`/`eLpNorm` two-norm handling: convert with
  `MeasureTheory.Lp.norm_eq_integral…`? for `p = 2` use
  `norm_toLp`… this bookkeeping is fiddly; a `private` lemma
  `‖(hf : MemLp f 2 μ).toLp _‖² = ∫ ‖f‖²` via
  `MemLp.norm_toLp`… search `Lp.norm_rpow_eq_...`, `L2.norm_sq_eq_inner`:
  `‖g‖² = re ⟪g,g⟫ = ∫ ‖g x‖²` — `inner_self`… use `L2.inner_def` at `g,g`).
- `continuous_integralOp_of_continuous`: uniform continuity of `K` on `X × X`
  (`CompactSpace.uniformContinuous_of_continuous`); then
  `|Tg x − Tg z| ≤ ‖K(x,·) − K(z,·)‖₂ ‖g‖ ≤ √μ(univ) · sup_y |K(x,y) − K(z,y)| ‖g‖`.
  Work with `Metric.continuous_iff`/ε-δ.
- `isPositive_mercerCLM`: `⟪T_K g, g⟫`… wait Mathlib `IsPositive` for CLMs:
  fields `IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x`
  (check `Mathlib/Analysis/InnerProductSpace/Positive.lean`).  Self-adjointness:
  `⟪T_K g, h⟫ = ⟪g, T_K h⟫` by Fubini + Hermitian symmetry of `K`
  (`hK.isKernelFun.conj_symm`); integrability for Fubini: continuity on the compact
  square + finite product measure (`MeasureTheory.integral_integral_swap` needs
  `Integrable (uncurry)` — from boundedness; or use
  `inner_mercerCLM` to write both sides as double integrals).  Positivity:
  approximate the double integral by quadratic forms — the book route (Prop 11.10)
  expands along an ONB of an RKHS; a MORE DIRECT route for `re ⟪g, T_K g⟫ ≥ 0`:
  simple functions: for indicator combinations the double integral is a limit of
  kernel quadratic forms (Riemann-style) — hard analytically.  RECOMMENDED route
  (the book's): let `H₀ := OfScalarKernel 𝕜 K`-style… we don't have an RKHS instance
  in scope here; INSTEAD use `Moore` (import chain already reaches it? Basic imports
  OrthonormalExpansion/Continuity → Basic → Reproducing — `Moore.lean` is NOT
  imported by Mercer/Basic; you may NOT add cross-lane imports?  Adding an import of
  another module's INTERFACE is allowed (it does not modify their files) — add
  `import StatLean.NonparametricStatistics.RKHS.Moore` to Mercer/Basic.lean if
  needed; then `H := OfScalarKernel 𝕜 K` with
  `haveI : Fact (IsKernelFun K) := ⟨hK.isKernelFun⟩` gives an RKHS with kernel `K`
  and a Hilbert basis (`exists_hilbertBasis`), `hasSum_scalarKernel` expands `K`,
  `tendstoUniformly_scalarKernel` upgrades to uniform, and then
  `⟪g, T_K g⟫ = lim ∑_{i∈s} |⟪toLp-class-of-eᵢ… |²`…  CAREFUL: members of the
  abstract RKHS are continuous?  Only via `continuous_coe_of_continuous_scalarKernel`
  ✓.  This mirrors the book's Prop 11.10 proof: for each finite partial sum,
  `∫∫ conj g(x) Kₛ(x,y) g(y) = ∑_{i∈s} |∫ eᵢ(x) conj g(x)…|² ≥ 0` — the finite
  Fubini swap is easy (finite sums of products of L¹ functions), and the uniform
  convergence `Kₛ → K` passes the double integral to the limit.
- `isMercerKernel_of_isPositive` (Prop 11.11): given distinct points and scalars,
  average the positive quadratic form `⟪T_K g, g⟫ ≥ 0` over
  `g = ∑ λᵢ μ(Uᵢ)⁻¹ 𝟙_{Uᵢ}` for small disjoint neighborhoods `Uᵢ ∋ xᵢ`
  (exist by Hausdorff/metric: `Metric.ball` with small radii + T2 disjointness), use
  continuity of `K` to control the error `≤ n² ε`, let `ε → 0`
  (`ge_of_tendsto`/`le_of_forall_pos_le_add`).  `IsOpenPosMeasure` gives
  `μ(Uᵢ) ≠ 0` (`Measure.IsOpenPosMeasure` API: `IsOpen.measure_pos`).
  Distinctness of the points: the `IsKernelFun` quantifier allows REPEATED points —
  reduce to distinct ones first (merge equal points' coefficients: group the sum by
  the value `x i` — `Finset.sum_comm`-style regrouping; a `private` lemma
  `IsKernelFun`-from-distinct-family suffices: prove positivity for families with
  `Function.Injective x`, then in general apply it to the image points with summed
  coefficients — `Finset.image` + `Finset.sum_image`-machinery, fiddly but
  elementary).
- `equicontinuous_integralOp` / `norm_integralOp_le_of_mem_ball`: the ε-δ estimate
  from `continuous_integralOp_of_continuous`, now uniform in `g` with `‖g‖ ≤ 1`
  (`Equicontinuous` unfolds via `Metric.equicontinuous_iff`? search; the estimate is
  identical), and pointwise Cauchy–Schwarz.

## Mercer/Compact.lean

- `norm_mercerCLM_le_of_bounded`: as `norm_mercerCLM_le` but with the sup bound:
  `‖T_S g x‖ ≤ ∫ |S x y| |g y| ≤ C ∫ |g| ≤ C √μ ‖g‖` then integrate:
  `‖T_S g‖₂ ≤ √μ · (C √μ ‖g‖) = μ(univ) C ‖g‖`.  (Cauchy–Schwarz for `∫ |g|`:
  `MemLp.integrable`… `L1` bound via Hölder: search `integral_norm_le`… use
  `norm_integralOp_le` + `‖symbolConjLp x‖ ≤ √(μ univ) C`.)
- `isCompactOperator_mercerCLM_finiteRank`: `T` maps into the span of
  `{toLp (f i) : i ∈ s}` (compute `T g = ∑_{i∈s} ⟪toLp (g i)…⟫ • toLp (f i)`-ish
  via linearity of the integral — `integralOp` of the finite-sum symbol separates),
  so it factors through a finite-dimensional subspace; a CLM with range in a
  finite-dim submodule is compact: `IsCompactOperator` of a map with
  `FiniteDimensional` range — search
  `isCompactOperator_of_finiteDimensional…`? if absent, prove: range ⊆ V findim ⇒
  image of unit ball is bounded subset of V ⇒ relatively compact
  (`IsCompact.closure_of_subset` + `Bornology.IsBounded` in findim:
  `Metric.isCompact_of_isClosed_isBounded` in finite dim / `FiniteDimensional.proper`);
  `IsCompactOperator` def: `∃ K, IsCompact K ∧ T ⁻¹' K ∈ 𝓝 0` — use
  `isCompactOperator_iff_isCompact_closure_image_ball`? (search the API in
  `Mathlib/Analysis/Normed/Operator/Compact.lean` — read that file first).
- `isCompactOperator_mercerCLM`: pick the RKHS `H := OfScalarKernel` route as above
  (import Moore if needed), Hilbert basis `e`, truncations
  `K_s(x,y) := ∑_{i∈s} (eᵢ x) conj (eᵢ y)`… relate `mercerCLM` of `K` and of `K_s`:
  `‖T_K − T_{K_s}‖ ≤ μ(univ) · sup |K − K_s| → 0` (uniform convergence
  `tendstoUniformly_scalarKernel` + `norm_mercerCLM_le_of_bounded` on the difference
  symbol — note `T_K − T_{K_s} = T_{K − K_s}` needs additivity of `mercerCLM` in the
  symbol: `private` lemma via `Lp.ext` + `integral_sub`), then
  `isCompactOperator_of_tendsto` along the `Finset`-filter (it takes a filter
  `l ≠ ⊥` and `Tendsto (fun i => T i) l (𝓝 T)` in operator norm — check exact
  signature; `atTop` on `Finset ι` is `NeBot` when `ι` nonempty — for `ι` empty,
  `K = 0` degenerate: handle `H` trivial case separately if needed).
  The eigenfunctions `eᵢ` here are continuous (needed for
  `isCompactOperator_mercerCLM_finiteRank`'s `C(X,𝕜)` signature): package each
  `eᵢ` as `ContinuousMap.mk _ (continuous_coe_of_continuous_scalarKernel …)`.

## Mercer/Theorem.lean — `exists_mercerEigensystem`

Assemble from Mathlib's spectral theorem
(`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`, section on compact operators):
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
  (hT : IsCompactOperator T) (hT' : T.IsSymmetric)`.
Plan:
1. `T := mercerCLM μ hK.continuous`; symmetric (`IsPositive.isSelfAdjoint` →
   `isSymmetric`… `ContinuousLinearMap.IsSelfAdjoint.isSymmetric`), compact
   (Compact.lean), positive (Basic.lean).
2. Eigenvalues are real and ≥ 0 (positivity: `⟪T e, e⟫ = λ ‖e‖² ≥ 0`).
3. For `λ ≠ 0`, `eigenspace T λ` is finite-dimensional
   (`ContinuousLinearMap.finite_dimensional_eigenspace` — check exact name/namespace
   in Spectrum.lean) — pick a finite orthonormal basis of each
   (`stdOrthonormalBasis` / `exists_orthonormalBasis`?  For a submodule use
   `OrthonormalBasis` of the subtype: `stdOrthonormalBasis 𝕜 (eigenspace …)` exists
   for finite-dim).
4. Index type `ι := Σ (λ : {λ : nonzero eigenvalues}), Fin (dim …)` — make it
   `Type` via an encoding; countability: the set of eigenvalues with `|λ| > 1/k` is
   finite for each `k` (else infinitely many orthonormal eigenvectors with
   `‖T eₙ‖ ≥ 1/k` contradict compactness — the image of the orthonormal sequence has
   no convergent subsequence: `‖T eₙ − T eₘ‖² = λₙ² + λₘ² ≥ 2/k²`; extract from
   `IsCompactOperator` via totally-bounded-image characterization).  This is real
   work — put it in `private` lemmas.  If a cleaner Mathlib route exists (search
   `IsCompactOperator` + `eigenvalue` + countable / `spectrum` countable:
   `IsCompactOperator.countable_spectrum`?), use it.
5. Continuity of eigenfunctions: `e = λ⁻¹ • T e` in `L²`; `T e` has the continuous
   representative `integralOp μ K e` (`mercerCLM_coeFn_ae`,
   `continuous_integralOp_of_continuous`); define
   `eigfun := ContinuousMap.mk (λ⁻¹ • integralOp μ K (toLp e)) …` and check
   `toLp eigfun = e` (a.e. identification; `IsOpenPosMeasure` needed to make
   `eigen_eq` hold EVERYWHERE: two continuous functions a.e.-equal on a
   full-support space are equal — search
   `Continuous.ae_eq_iff_eq` in `Mathlib/MeasureTheory/Function/ContinuousMapDense`
   or `Measure.eqOn_of_ae_eq` + `IsOpenPosMeasure`).
6. `opExpansion`: decompose `g = g₀ + ∑ projections` with
   `g₀ ∈ (⨆ eigenspaces)ᗮ ⊕ eigenspace 0`-analysis: from the spectral theorem the
   closure of the sup of ALL eigenspaces is ⊤; `T` kills `eigenspace 0` and acts by
   `λ` on each; sum over our `ι` (Hilbert-basis-of-the-closure argument:
   the family (eigvecs over ι) ∪ (any ONB of ker T) is a Hilbert basis of `L²`;
   then `T g = ∑ λᵢ ⟪eᵢ, g⟫ eᵢ` by continuity of `T` applied to the basis
   expansion of `g`).  Formalize with `HilbertBasis.hasSum_repr` +
   `ContinuousLinearMap.hasSum`.

Then `MercerEigensystem.hasSum_kernel` / `tendstoUniformly_kernel`: the book's
positivity-of-residuals + Dini.  Residual kernel
`K_s(x,y) := K(x,y) − ∑_{i∈s} λᵢ eᵢ(x) conj (eᵢ y)` is continuous and POSITIVE
(its integral operator is `T` minus the spectral truncation, positive by the
expansion — Prop 11.11 converts back to pointwise PSD), so its diagonal is ≥ 0:
`∑_{i∈s} λᵢ ‖eᵢ x‖² ≤ K(x,x) ≤ sup K` — hence the diagonal series converges
pointwise; monotone limits of continuous functions… for pointwise convergence of the
diagonal to exactly `K(x,x)`: the deficit `d(x) := K(x,x) − ∑_{i} λᵢ‖eᵢ x‖²` is
a nonneg continuous?… `d` is only upper-semicontinuous a priori — the book instead
shows `‖T_{K_∞}‖ = lim λ = 0` forcing `K_∞ ≡ 0` — mirror the book: the residual
kernels' operators have norms `→ 0`?  With OUR spectral route the residual operator
is `0` in the limit in operator norm on the nonzero part;
`T_{K_s} → 0`… then `K_∞` is a continuous kernel whose operator is `0` ⇒ by the
averaging argument (Prop 11.11 machinery) `K_∞ ≡ 0` pointwise (full support!) ⇒
pointwise convergence; absolute+uniform then follow from Dini on the diagonal +
Cauchy–Schwarz (same pattern as `tendstoUniformly_scalarKernel`).
`summable_eigval`/`hasSum_eigval`: integrate the uniform expansion over the diagonal
(swap `∫` and uniform limit: `TendstoUniformly.integral_tendsto`? search
`MeasureTheory.tendstoUniformly` integral swap —
`TendstoUniformly.tendsto_integral…`; `∫ eᵢ conj eᵢ = ‖eᵢ‖² = 1`).

## Mercer/SquareRoot.lean

Use `opExpansion` and the `L²`-side systematically; realize `H(K)`-side statements
through `rangeSpace_*` (RangeSpace.lean) where convenient, plus `Uniqueness`-free
arguments: statements are phrased against an arbitrary `[RKHS 𝕜 H X 𝕜]` with
`scalarKernel H = K`.  Suggested order: `continuous_boxProd`, `mercerCLM_comp_self`
(Fubini on the compact square), `isMercerKernel_trace_smul_sub_boxProd` (the book's
Cholesky argument: `L_t(x,y) := K(t,t)K(x,y) − K(x,t)K(t,y)` is PSD for each `t` —
prove via the 2×2-minor/Cauchy–Schwarz inequality in the RKHS:
`|K(x,t)|² ≤ K(x,x)K(t,t)` generalized — actually `L_t` is the kernel of functions
vanishing at `t`: prove PSD directly:
`∑ᵢⱼ conj aᵢ aⱼ L_t(xᵢ,xⱼ) = K(t,t)·Q − |∑ᵢ conj aᵢ K(xᵢ,t)|²`-shaped; use
Cauchy–Schwarz in `H(K)`… concretely with kernel functions:
`= K(t,t) ‖u‖² − |⟪u, k_t⟫|² ≥ 0` where `u := ∑ aᵢ k_{xᵢ}` — needs an RKHS for `K`;
obtain one via `OfScalarKernel` as before), then integrate over `t`.
For `sqrtSymbol`: sections in `L²` via the eigen-expansion Parseval
(`∫ |S(x,y)|² dμ(y) = ∑ λᵢ |eᵢ(x)|² ≤ K(x,x)` — orthonormality),
`sqrtCLM` fields like `mercerCLM`'s, `sqrtCLM_hasSum` from orthonormality
(`⟪toLp eᵢ, ·⟫` of the tsum — swap via continuity), positivity and `T_S² = T_K`
from the diagonal expansions, and the `H(K)` statements via Papadakis-style
recognition: `{√λᵢ eᵢ}` expands `K` pointwise (that IS `hasSum_kernel`), so by
`isParsevalFrame_of_hasSum_scalarKernel`?? — that requires the family to LIVE in `H`;
get them into `H`: `√λᵢ eᵢ = T_S`-image… fallback: prove membership via
`range_integralOp_eq_range_coe` for the symbol `sqrtSymbol` (RangeSpace gives an
RKHS with kernel `S □ S* = K` (compute!), and `Uniqueness.lean`'s
`exists_isometryEquiv_of_scalarKernel_eq` transfers everything to the given `H`) —
importing Uniqueness/Papadakis/ParsevalFrame into SquareRoot is allowed.
`mem_range_coe_iff_summable` then follows from the ONB expansion in `H`.
Work incrementally; leave documented sorries where an ingredient is missing.
