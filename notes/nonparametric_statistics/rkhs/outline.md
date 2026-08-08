# RKHS batch — outline (book ↔ Lean dictionary)

Reference: Paulsen & Raghupathi, *An Introduction to the Theory of Reproducing Kernel
Hilbert Spaces* (CUP, 2016). PDF: `ref/Nonparametric/RKHS.pdf`. Plan: `RKHS_plan.md`
(chapters 1 §1.1 + §1.3.1, 2 §2.1–2.4, 8 §8.2/8.5–8.6 + representer, 11 §11.3).

**Citation convention (UPDATED 2026-08-05, user request):** every module docstring carries a
`**Reference.**` block citing Paulsen–Raghupathi with chapter/§/item numbers and a
`**Proof formalization notes.**` block (YangBarron style), before `**Bibliographic
comments.**`, which continue to cite the *original* literature (Aronszajn 1950, Moore 1935,
Mercer 1909, Larson, Papadakis, Kimeldorf–Wahba 1971, Boser–Guyon–Vapnik 1992, …).
`-- USER-INPUT:`/`-- LEAN-ONLY:` tags state the mathematical claim; this ledger remains the
authoritative book↔Lean dictionary.

**The big reuse**: our Mathlib pin (`5e932f97`, v4.29.1) contains
`Mathlib.Analysis.InnerProductSpace.Reproducing` — the (vector-valued) `RKHS 𝕜 H X V`
class *based on this very book*, with `kerFun`, `kernel` (as `Matrix X X (V →L[𝕜] V)`),
reproducing lemmas `kerFun_inner`/`inner_kerFun`, `kerFun_dense` (= Prop 2.1),
`isHermitian_kernel`, `posSemidef_kernel` (⊇ Prop 2.13), `posSemidef_tfae`, and
`RKHS.OfKernel` + `kernel_ofKernel` (= Moore's Thm 2.14 in matrix form).
We build the *scalar* (V := 𝕜) theory of the book on top of it.

Mathlib inner-product convention: `⟪·,·⟫_𝕜` is **conjugate-linear in the FIRST slot**
(book is conjugate-linear in the second). Book's `f(x) = ⟨f, k_x⟩` becomes
`f x = ⟪kernelFun H x, f⟫_𝕜`. Book's `K(x,y) = k_y(x)` is kept verbatim:
`scalarKernel H x y = (kernelFun H y) x = kernel H x y 1`.

## Directory & namespace

`StatLean/NonparametricStatistics/RKHS/` (+ `RKHS/Mercer/`), namespace
`StatLean.NonparametricStatistics` (area convention; avoids shadowing Mathlib's `RKHS`
namespace). Umbrella wiring into `StatLean/NonparametricStatistics.lean` is laptop-only,
done at merge.

## File plan and P&R dictionary

| File | P&R | Content |
|---|---|---|
| `RKHS/Basic.lean` | Def 1.1, 1.2; Lem 2.2; p.4 identities | `kernelFun H x := kerFun H x 1`, `scalarKernel`; `f x = ⟪kernelFun x, f⟫`; `scalarKernel x y = ⟪kernelFun y, kernelFun x⟫`; hermitian symmetry; `‖kernelFun x‖² = K(x,x)`; norm-lim ⇒ pointwise-lim |
| `RKHS/KernelFunction.lean` | Def 2.12, Prop 2.13, Prop 2.23, §8.2 | `IsKernelFun K` (finite PSD quadratic form); Gram/feature kernels `fun x y => ⟪φ x, φ y⟫` are kernel functions (conj-orientation fixed to Mathlib's); `IsKernelFun (scalarKernel H)`; Grammian `Matrix.of fun i j => ⟪h i, h j⟫` PSD, PD ↔ lin. indep. |
| `RKHS/OrthonormalExpansion.lean` | Thm 2.4 | `HilbertBasis ι 𝕜 H` ⇒ `HasSum (fun i => conj (e i y) * (e i x)) (scalarKernel H x y)` (pointwise, unordered); diag case `∑ ‖e i x‖² = K(x,x)` |
| `RKHS/Subspace.lean` | Thm 2.5 | closed `H₀ : Submodule 𝕜 H` is an RKHS (instance), `scalarKernel H₀ x y = ⟪P₀ (kernelFun y), kernelFun x⟫` |
| `RKHS/Continuity.lean` | Thm 2.17 (+ ‖ky−ky₀‖² identity) | `Continuous (scalarKernel ·×·)` ⇒ every `f : H` continuous; also `Continuous (kernelFun H ·)` |
| `RKHS/ParsevalFrame.lean` | Def 2.6, Prop 2.7, 2.8, 2.9 | general Hilbert `IsParsevalFrame f`; projection of ONB is frame; TFAE (frame ↔ analysis isometry into `lp 2` ↔ reconstruction `HasSum`); + polarization; Larson dilation |
| `RKHS/Papadakis.lean` | Thm 2.10 | frame ↔ `HasSum (fun s => f s x * conj (f s y)) (scalarKernel x y)` |
| `RKHS/Moore.lean` | Thm 2.14, Def 2.15, Rem 2.16 | scalar wrapper of `RKHS.OfKernel`: `IsKernelFun K` → PSD matrix over `V=𝕜` (`Fact` bridge) → space `OfScalarKernel K` with `scalarKernel (OfScalarKernel K) = K` |
| `RKHS/Uniqueness.lean` | Prop 2.3 | two RKHSs w/ equal scalar kernels: `∃ e : H₁ ≃ₗᵢ H₂` commuting with evaluation (hence same function ranges, equal norms) |
| `RKHS/RankOne.lean` | Prop 2.19 | `K = f(x)·conj (f y)` is a kernel fun; in any RKHS w/ this kernel: range coe = 𝕜∙f, the rep of f has norm 1 (f ≠ 0) |
| `RKHS/InnerKernel.lean` | Def 2.22 (Grammian in KernelFunction), Prop 2.24 | RKHS instance on `L` itself w/ `coeCLM w = fun v => ⟪v, w⟫`; `kernelFun x = x`, `scalarKernel x y = ⟪x, y⟫`; range = dual functionals, norms match |
| `RKHS/MinKernel.lean` | Lem 2.20, Prop 2.21 | all-ones `Jₙ` PSD + eigenvalues {0,n}; `min` kernel on `[0,∞)` is a kernel fun (indicator feature map `t ↦ χ_[0,x]` in L²) |
| `RKHS/Sobolev.lean` | §1.3.1 | H := {x ↦ ∫₀ˣ g, g ∈ L²[0,1], ∫₀¹g = 0} realized as the closed subspace `(ℝ∙1)ᗮ ⊆ L²[0,1]` with `coeCLM g x = ⟪χ_[0,x] − x·1, g⟫`-style eval; RKHS instance; `scalarKernel x y = min x y − x*y`; `‖kernelFun x‖² = x(1−x)`. *Deviation*: book defines H via absolute continuity and proves the integral representation; we take the representation as the definition (the book's own §11.2.1 characterization). |
| `RKHS/FeatureMap.lean` | §8.2 | `featureKernel φ := fun x y => ⟪φ x, φ y⟫` (orientation per Mathlib), `IsKernelFun (featureKernel φ)`; every RKHS kernel is a feature kernel via `φ = kernelFun` |
| `RKHS/Separation.lean` | Def 8.1, Lem 8.2, Prop 8.3 | real Hilbert; `SeparatesData v c x λ` (finite data `Fin n`); `dist x {y | ⟪y,v⟫=c} = |⟪x,v⟫−c|/‖v‖`; separating v replaceable by its span-projection |
| `RKHS/MaxMargin.lean` | Def 8.5, Thm 8.6 | feasible set `C = {v | ∃ c, ∀ i, λ i * (⟪x i, v⟫ − c) ≥ 1}` closed convex; separability(finite, strict) ⇒ C nonempty; ∃! min-norm `w ∈ C`; `w ∈ span (range x)`; margin optimality: (w,c) maximizes `min_i dist(x i, V)` over separating hyperplanes |
| `RKHS/Representer.lean` | Thm 8.7, Thm 8.8 | `J f = W ‖f‖² + L (fun i => f (x i))`, `StrictMono W`, minimizer ⇒ ∈ span kernelFuns (weak-mono version: projection is also a minimizer); `J f = ‖f‖² + L ∘ eval`, `ConvexOn L` (+continuity) ⇒ ∃! minimizer |
| `RKHS/IntegralOperator.lean` | Def 11.1, Prop 11.2 | `(Y,μ)` measure space, symbols `S : X → Y → 𝕜` with `∀x, MemLp (S x) 2`; `integralOp S g x = ∫ S x y * g y`; `boxProd`; `symbolAdjoint`; `IsKernelFun (S □ S*)` |
| `RKHS/RangeSpace.lean` | Thm 11.3, Cor 11.4 | RKHS instance on `(ker)ᗮ` model of the range with Sarason norm; range functions = H(S□S*); `‖f‖ = inf{‖g‖ : T_S g = f}`; isometry `U : H(K) → L²`, `U (kernelFun x) = conj ∘ S x`-class |
| `RKHS/Mercer/Defs.lean` | Def 11.5 | `X` compact metric, `μ` finite Borel; `MercerKernel K` = continuous + `IsKernelFun`; `mercerOp K : L²(μ) →L L²(μ)` and pointwise version into `C(X)` |
| `RKHS/Mercer/Basic.lean` | Prop 11.6–11.12 | norm comparisons; separability of H(K); **Dini** uniform+absolute ONB-series convergence; boundedness + continuous range; positivity of `T_K`; converse (full support); equicontinuity of `T_K(ball)` |
| `RKHS/Mercer/OperatorLemmas.lean` | Lem 11.13, 11.14 | norm-attaining vector: `‖Ah‖ = ‖A‖`, `k ⊥ h` ⇒ `Ak ⊥ Ah`; positive op: norm-attaining unit vector is eigenvector w/ eigenvalue ‖P‖ |
| `RKHS/Mercer/Compact.lean` | (route lemma) | `T_K` is a compact operator: finite-rank approximants from the truncated ONB series (Prop 11.8) + `isCompactOperator_of_tendsto` |
| `RKHS/Mercer/Theorem.lean` | **Thm 11.15** | countable orthonormal continuous eigenfunctions, positive eigenvalues, `T_K g = ∑ λ n ⟪e n, g⟫ e n`, `K(x,y) = ∑ λ n * e n x * conj (e n y)` (uniform absolute convergence). Route: Mathlib compact-self-adjoint spectral theorem + positivity, not P&R's Ascoli iteration. |
| `RKHS/Mercer/SquareRoot.lean` | Prop 11.16, 11.17, Thm 11.18 | `T_K²` symbol `K⁽²⁾`; `C·K − K⁽²⁾` Mercer + `range T_K ⊆ H(K)`; sqrt symbol `S = ∑ √λ e e*`: bounded, `T_S ≥ 0`, `T_S² = T_K`, `range T_S = H(K)`, isometry on `(ker T_K)ᗮ`, `{√λ n · e n}` ONB of `H(K)`, membership test `∑ |αn|²/λn < ∞` |

Skipped (no numbered statement in scope): §1.2 examples, §2.3.3 positive-matrix RKHS
(prose only), Prop 8.4 (not requested; heavy dual-basis construction), §11.4
(Hilbert–Schmidt ↔ L² symbols; out of plan scope).

## Lanes (pairwise file-disjoint touch-sets)

| Lane branch | Files | Wave |
|---|---|---|
| `np/rkhs-core` | Basic, KernelFunction, OrthonormalExpansion, Subspace, Continuity | 1 |
| `np/rkhs-frames` | ParsevalFrame, Papadakis | 1 |
| `np/rkhs-sobolev` | MinKernel, Sobolev | 1 |
| `np/rkhs-moore` | Moore, Uniqueness, RankOne, InnerKernel | 2 |
| `np/rkhs-ml` | FeatureMap, Separation, MaxMargin, Representer | 2 |
| `np/rkhs-integral` | IntegralOperator, RangeSpace, Mercer/Defs, Mercer/OperatorLemmas | 2 |
| `np/rkhs-mercer` | Mercer/Basic, Mercer/Compact, Mercer/Theorem, Mercer/SquareRoot | 3 |

All statements are laptop-authored stubs on `np/rkhs` (stub-gated green-with-sorries
before any lane launches); lanes only close proofs and may add `private` helpers in
their own files. Cross-lane imports go through stub statements — allowed.

## Verified Mathlib bricks (pin 5e932f97)

- `Mathlib.Analysis.InnerProductSpace.Reproducing`: `RKHS`, `RKHS.kerFun`,
  `RKHS.kernel`, `kerFun_inner`, `inner_kerFun`, `kerFun_dense`, `isHermitian_kernel`,
  `posSemidef_kernel`, `posSemidef_tfae`, `OfKernel`, `kernel_ofKernel`.
- `Mathlib.Analysis.InnerProductSpace.Spectrum`:
  `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`
  (compact self-adjoint spectral theorem, hyps `IsCompactOperator T`, `T.IsSymmetric`),
  `ContinuousLinearMap.finite_dimensional_eigenspace`,
  `eq_zero_of_forall_hasEigenvalue_eq_zero`.
- `Mathlib.Topology.UniformSpace.Dini`: `Monotone.tendstoUniformly_of_forall_tendsto`,
  `Antitone.tendstoUniformly_of_forall_tendsto` (+ `On` variants).
- `Mathlib.Analysis.Normed.Operator.Compact` (module name to verify):
  `IsCompactOperator`, `isCompactOperator_of_tendsto`,
  `isClosed_setOf_isCompactOperator`.
- Hilbert projection: `exists_norm_eq_iInf_of_complete_convex`,
  `norm_eq_iInf_iff_real_inner_le_zero`.
- Convex minorants: `ConvexOn.exists_affine_le_of_lt` (& `_real` variants).
- `HilbertBasis` (`Mathlib.Analysis.InnerProductSpace.l2Space`): `repr`, `hasSum_repr`,
  `exists_hilbertBasis`; `lp.single`.
- `MeasureTheory.L2Space`: `MemLp.integrable_mul`, `L2.inner_def`; `indicatorConstLp`.
- Known split-module gotchas (memory): `…Integral.Lebesgue.Basic`, `…Measure.Prod`,
  `…Instances.ENNReal.Lemmas`, `…InnerProductSpace.PiL2`.
