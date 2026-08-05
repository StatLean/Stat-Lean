FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-mercer2 — Mercer's theorem assembly, square-root section, Riesz debt

This is the FINAL lane of the batch.  Everything else is proved and 0-sorry: all of
Mercer/Basic (Props 11.6–11.12 incl. `isPositive_mercerCLM` and
`isMercerKernel_of_isPositive`), Mercer/Compact (`isCompactOperator_mercerCLM`),
Mercer/OperatorLemmas, IntegralOperator, RangeSpace, and the BoxSquare section of
SquareRoot.  Every remaining `sorry` carries an `-- OPEN.` comment written by the
previous session with the intended route — READ THOSE COMMENTS FIRST; they are accurate
and were written after proving the neighboring lemmas.

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/Mercer/Theorem.lean   (5 sorries)
- StatLean/NonparametricStatistics/RKHS/Mercer/SquareRoot.lean (13 sorries)
- StatLean/NonparametricStatistics/RKHS/InnerKernel.lean       (1 sorry)

Build targets: `lake build StatLean.NonparametricStatistics.RKHS.Mercer.Theorem`
(then Mercer.SquareRoot, InnerKernel).

## Priorities (bank progress in this order)

1. **InnerKernel.lean `dualRKHS_range_coe`** (quick win): Riesz–Fréchet for
   conjugate-linear functionals.  `⊆`: for `w : L` the function is `v ↦ ⟪v, w⟫_𝕜`;
   exhibit `T : L →L⋆[𝕜] 𝕜` — build with `LinearMap.mkContinuous` over the semilinear
   `LinearMap` (`{ toFun := fun v => ⟪v, w⟫_𝕜, map_add' := inner_add_left,
   map_smul' := inner_smul_left }` — check the `RingHom` orientation:
   `map_smul' : f (c • v) = starRingEnd 𝕜 c • f v` matches `inner_smul_left`), bound by
   Cauchy–Schwarz.  `⊇`: given `T : L →L⋆[𝕜] 𝕜`, the map `v ↦ conj (T v)` is a `𝕜`-linear
   continuous functional (compose with `RCLike.conjCLE`? — if bundling fights you, apply
   Riesz `InnerProductSpace.toDual` to the LINEAR functional `v ↦ conj (T v)`:
   `toDual.symm` gives `w` with `⟪w, v⟫ = conj (T v)` for all `v`
   (`InnerProductSpace.toDual_symm_apply`), hence `T v = conj ⟪w, v⟫ = ⟪v, w⟫` ✓ and the
   representing element is `w`).  Then `funext` + the coeCLM computation
   (`dualRKHS`'s coe is definitionally `fun v => ⟪v, w⟫`).
2. **Theorem.lean `exists_mercerEigensystem`** — the summit.  The `-- OPEN.` comment
   lists the three missing ingredients (a) countability, (b) `Type 0` encoding,
   (c) `opExpansion`.  Suggested concrete plan:
   - Let `T := mercerCLM μ hK.continuous`, `hTpos := isPositive_mercerCLM hK`,
     `hTc := isCompactOperator_mercerCLM hK`, `hTsym := hTpos.isSelfAdjoint.isSymmetric`
     (check exact name for CLM selfAdjoint → LinearMap.IsSymmetric — search
     `IsSelfAdjoint.isSymmetric` in `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`).
   - (a) For `ε > 0`, any orthonormal family of eigenvectors with eigenvalues `≥ ε` is
     finite: if infinite, pick a countable subfamily `eₙ`; `T eₙ = λₙ eₙ` with
     `‖T eₙ − T eₘ‖² = λₙ² + λₘ² ≥ 2ε²` (orthogonality + Pythagoras), contradicting
     that `closure (T '' ball 0 1)` is compact hence sequentially compact
     (`IsCompactOperator` def: `∃ K, IsCompact K ∧ T ⁻¹' K ∈ 𝓝 0`; extract via
     `IsCompact.isSeqCompact` / `IsCompact.tendsto_subseq`).  Package as: the eigenvalue
     set `Λ := {λ : ℝ | 0 < λ ∧ HasEigenvalue T λ}`… work instead with an explicit
     orthonormal basis construction below and prove countability of the INDEX at the end
     (`Set.Countable` of a union over `k : ℕ` of finite sets, `Set.countable_iUnion`).
   - (b) Rather than a sigma over eigenvalues, build the system as follows: `L²(X,μ)` is
     separable — prove via `TopologicalSpace.SeparableSpace` instance search:
     `MeasureTheory.Lp` has a `SecondCountableTopology` instance for a second-countable
     `X` + separable `𝕜`?  search `instSecondCountableTopologyLp` /
     `MeasureTheory.Lp.secondCountableTopology`; `X` compact metric IS second countable.
     If found: every orthonormal family in a separable space is COUNTABLE
     (search `Orthonormal.countable` / prove: orthonormal vectors are `√2`-separated, a
     separable metric space has no uncountable `√2`-separated set —
     `Set.Countable` via `TopologicalSpace.SeparableSpace` + pairwise-disjoint balls;
     Mathlib may have `Set.PairwiseDisjoint.countable_of_isOpen` or
     `_root_.Set.Countable` of separated sets — search `separated` `countable`
     in `Mathlib/Topology/Bases.lean`, e.g. `TopologicalSpace.IsSeparable` API).  Then:
     take a MAXIMAL orthonormal set `B` of eigenvectors of `T` with positive eigenvalues
     (Zorn, `zorn_subset`-style, or `exists_maximal_orthonormal` — search that name in
     `Mathlib/Analysis/InnerProductSpace/Projection` or `l2Space`); it is countable, so
     `∃ f : ℕ ↪ …` or an equiv with an encodable index; define `ι := {n : ℕ // …}`-style
     via `Set.Countable` → `Encodable` (`Set.Countable.toEncodable`) and reindex through
     `Encodable.encode`… KEEP IT SIMPLE: `d.ι := ↥S` won't be `Type 0` if `L²` is large —
     so reindex: a countable set `S` admits an injection to `ℕ`
     (`Set.Countable.exists_injective_nat`? — no: use `hS.toEncodable` then the range of
     `encode` in `ℕ`); define `ι := {n : ℕ | n ∈ Set.range (encode on S)}` and pull the
     data back along the inverse.  This bookkeeping is the (b) step; bank it as private
     defs/lemmas with incremental commits.
   - Eigenfunction continuity + `eigen_eq` everywhere: for an eigenvector `e` (class in
     `L²`) with eigenvalue `λ > 0`, `e = λ⁻¹ • T e` in `L²`; `integralOp μ K e` is a
     continuous representative (`continuous_integralOp_of_continuous`,
     `mercerCLM_coeFn_ae`); define `eigfun := ⟨λ⁻¹ • integralOp μ K e, …⟩ : C(X,𝕜)` and
     prove `ContinuousMap.toLp … eigfun = e` (`Lp.ext` + a.e. agreement) and the
     pointwise `eigen_eq` — first a.e., then everywhere: two continuous functions equal
     a.e. w.r.t. a measure of full support are equal — search
     `Continuous.ae_eq_iff_eq` (exists in `Mathlib/MeasureTheory/Measure/OpenPos.lean`
     as `Measure.eq_of_ae_eq`-style: `IsOpenPosMeasure` section has
     `Continuous.ae_eq_iff_eq`).
   - (c) `opExpansion`: maximality of `B` means `(span B)ᗮ ∩ (ker T)ᗮ = 0`… Show: for
     `g ⊥ span B` and `g ⊥ ker T`, `g = 0`.  Consider `T` restricted to the closed
     subspace `M := (span B ∪ ker T)ᗮ`: it is invariant (self-adjointness), compact,
     self-adjoint, nonzero norm would produce (via
     `isEigenvector_of_norm_attaining` — Mercer/OperatorLemmas, PROVED — applied to a
     norm-attaining sequence… ATTENTION: compact operators DO attain their norm:
     take `gₙ` unit with `‖T gₙ‖ → ‖T‖`, extract a convergent subsequence of `T gₙ`
     (compactness), get `h` with… the standard argument uses weak compactness; a
     self-contained route: `‖T‖² = ‖T* T‖`… If norm-attainment is painful, use instead
     Mathlib's spectral machinery directly:
     `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTsym` says
     the closure of the span of ALL eigenspaces is ⊤; eigenspaces for `λ ≤ 0`:
     positivity forces `λ ≥ 0` (an eigenvector with `λ < 0` has
     `re ⟪T e, e⟫ = λ ‖e‖² < 0`), and `eigenspace T 0 = ker T`; so
     `(span B)ᗮ ∩ (ker T)ᗮ ⊆ …` reduce to: `B` maximal ⇒ `span B` dense in the span of
     the positive eigenspaces (a nonzero vector of `eigenspace T λ ⊖ span B` could be
     added to `B` after normalizing — contradicting maximality; mind vectors MIXING
     eigenspaces: decompose via the iSup and work eigenvalue-by-eigenvalue:
     `Submodule.iSup...`; the pairwise-orthogonality of distinct eigenspaces is
     `hTsym.orthogonalFamily_eigenspaces` — search exact name).  Then for any `g`:
     `g = g₀ + ∑ ⟪eₙ, g⟫ eₙ` with `g₀ ∈ ker T` (Hilbert-basis expansion of the closure
     decomposition: `Submodule.starProjection` onto `ker T` and onto the closed span;
     apply `T` continuously: `T g = ∑ λₙ ⟪eₙ, g⟫ eₙ` (`ContinuousLinearMap.hasSum`)). ✓
3. **`hasSum_kernel`** — follow its `-- OPEN.` comment (residual kernels; both halves of
   the needed machinery — `isMercerKernel_of_isPositive` and the operator-norm bound
   `norm_mercerCLM_le_of_bounded` — are PROVED).  The missing "residual operator norms
   → 0": from `d.opExpansion`, `T_{K_s} = T_K − (truncation)` and for unit `g`,
   `‖T_{K_s} g‖² = ∑_{n ∉ s} λₙ² |⟪eₙ,g⟫|² ≤ (sup_{n ∉ s} λₙ) ⟪T_K g, g⟫`-style bounds;
   `sup_{n ∉ s} λₙ → 0` along `atTop : Finset ι` because `(λₙ)` is summable…
   CAREFUL: summability of eigenvalues is stated LATER (`summable_eigval`) and its
   proof note routes through `hasSum_kernel` — avoid circularity: derive
   `λₙ → 0` (cofinitely small) directly from compactness (same ε-finiteness argument as
   in (a): only finitely many `n` with `λₙ ≥ ε`), which needs no summability.  Then
   `‖T_{K_s}‖ ≤ sup_{n∉s} λₙ → 0` (spectral bound for the positive operator `T_{K_s}`
   via its own expansion: `re ⟪T_{K_s} g, g⟫ = ∑_{n∉s} λₙ |⟪eₙ,g⟫|² ≤ ε ‖g‖²` and a
   positive operator has `‖P‖ ≤ C` iff `re ⟪P g, g⟫ ≤ C ‖g‖²` — search
   `ContinuousLinearMap.IsPositive` norm characterizations / `opNorm_le_bound` with the
   polarization trick; if the sharp bound fights you, use
   `‖P‖ ≤ 2 sup re⟪Pg,g⟫`-style with any constant — only `→ 0` matters).
   Final pointwise step: `K_∞ := K − ∑` has vanishing operator, and BOTH `±K_∞` satisfy
   `isMercerKernel_of_isPositive`'s hypotheses (hermitian, continuous, positive operator
   `0`), so `K_∞` and `−K_∞` are both PSD ⇒ diagonal `= 0` ⇒ `K_∞ ≡ 0` via the PSD
   2×2-minor bound `|K_∞(x,y)|² ≤ K_∞(x,x) K_∞(y,y)` (prove from `IsKernelFun` with the
   2-point family — a small private lemma).
4. **`tendstoUniformly_kernel`, `summable_eigval`, `hasSum_eigval`** — per their
   comments; the analogous proved patterns are in Mercer/Basic
   (`tendstoUniformly_diag`, `tendstoUniformly_scalarKernel`).
5. **SquareRoot section** — after `hasSum_kernel`; each sorry has its route in the
   prompt of the previous session and the `-- OPEN.` comments; use RangeSpace
   (`rangeSpace_scalarKernel` etc., all PROVED) + Uniqueness
   (`exists_isometryEquiv_of_scalarKernel_eq`, PROVED) + Papadakis
   (`isParsevalFrame_of_hasSum_scalarKernel`, PROVED) as building blocks.

If time runs short, a fully-proved 1–3 with documented 4–5 beats a half-broken sweep.
Commit after EVERY closed lemma.  Never touch files outside the touch-set.
