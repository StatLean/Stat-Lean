# RKHS batch — status

Integration branch: `np/rkhs` (off local main `cd41a7d9`).  See `outline.md` for the
book↔Lean dictionary and lane plan.

## Phase log

- 2026-08-05: 25 stub files + umbrella `StatLean/NonparametricStatistics/RKHS.lean`
  authored on laptop (statement-first, all proofs `sorry`).  NOT yet wired into the area
  umbrella `StatLean/NonparametricStatistics.lean` (done at merge, laptop-only).
- 2026-08-05: **stub gate GREEN** after 6 rounds (`Build completed successfully, 2816
  jobs`, 145 sorries).  Notable elaboration finding: `CompleteSpace ↥H₀` synthesized
  bare does not match `kernelFun`'s recorded norm-chain uniformity at instance
  transparency — resolved by explicit-instance wrappers
  (`sobolevKernelFun`, `rangeSpaceKernelFun`, `@kernelFun … hc …` in Subspace).
  Statement repair at stub time: `SeparatesData.ne_zero` needs both label signs.
  Wave-1 fan-out launched (core, frames, sobolev).

## Lane status

| Lane | Branch | Files | State |
|---|---|---|---|
| core | `np/rkhs-core` | Basic, KernelFunction, OrthonormalExpansion, Subspace, Continuity | MERGED 0-sorry |
| frames | `np/rkhs-frames` | ParsevalFrame, Papadakis | MERGED 0-sorry |
| sobolev | `np/rkhs-sobolev` | MinKernel, Sobolev | MERGED 0-sorry |
| moore | `np/rkhs-moore` | Moore, Uniqueness, RankOne, InnerKernel | MERGED; exists_rkhs repaired+proved on laptop; dualRKHS_range_coe restated (conj-linear), 1 sorry to residual pass |
| ml | `np/rkhs-ml` | FeatureMap, Separation, MaxMargin, Representer | MERGED; MaxMargin degeneracy repaired+proved on laptop |
| integral | `np/rkhs-integral` | IntegralOperator, RangeSpace, Mercer/Defs, Mercer/OperatorLemmas | MERGED 0-sorry |
| mercer | `np/rkhs-mercer` | Mercer/Basic, Mercer/Compact, Mercer/Theorem, Mercer/SquareRoot | MERGED: Basic+Compact 0-sorry (11.6–11.12, T_K compact), BoxSquare (11.16/11.17) closed; Thm 11.15 assembly + 11.18 open w/ routes |
| mercer2 | `np/rkhs-mercer2` | Mercer/Theorem, Mercer/SquareRoot, InnerKernel | MERGED: Theorem.lean 0-sorry (THM 11.15 COMPLETE incl. trace formula), InnerKernel 0-sorry; sqrtSymbol tsum-def refuted (circle counterexample) |
| sqrt | `np/rkhs-sqrt` | Mercer/SquareRoot | MERGED 0-sorry — THM 11.18 complete against the repaired L²-limit definition |

## Known design decisions / deviations (documented in file docstrings)

- Sobolev §1.3.1: absolute continuity replaced by the integral-representation model
  (carrier = mean-zero subspace of `L²[0,1]`); completeness inherited from `L²`.
- `IsKernelFun` builds in Hermitian symmetry (needed over `ℝ`; automatic over `ℂ`).
- Mercer proved via Mathlib's compact-self-adjoint spectral theorem + Dini, not P&R's
  Arzelà–Ascoli iteration; equicontinuity (Prop 11.12) kept as standalone result.
- Thm 8.7 needs `StrictMono W` for "every minimizer in span" (book's "monotonically
  increasing" is used strictly in its proof); weak `Monotone` version states the
  projection is again a minimizer.
- Thm 8.8 existence: continuity of the convex loss on the finite-dimensional value
  space is derived (convex ⇒ continuous in finite dim), not assumed.
- Expected statement-risk hot spots for the stub gate: `MemLp.toLp` argument order,
  `ContinuousMap.toLp` argument order, `Submodule.starProjection` instance resolution,
  `LinearMap.mkContinuousOfExistsBound` field names, FunLike coercion `(f : X → 𝕜)`.

## Statement renegotiations (lane findings, laptop-adjudicated)

- `SeparatesData.ne_zero` (pre-fan-out): false without both label signs; inputs
  `0 < lab iPos`, `lab iNeg < 0` added.
- `IsKernelFun.exists_rkhs`: `∃ H : Type _` auto-bound an independent universe — false
  (lane counterexample: discrete kernel on large `X`); pinned to `Type (max uK uX)` and
  proved on the laptop from `scalarKernel_ofScalarKernel`.
- `dualRKHS_range_coe`: 𝕜-linear-functional form FALSE over ℂ (lane machine-checked
  counterexample `dualRKHS_range_coe_false`, kept in-file); restated with `L →L⋆[𝕜] 𝕜`
  (Riesz–Fréchet for conjugate-linear functionals).  Proof deferred to residual pass.

## Statement renegotiations (continued)

- `isMaxMarginHyperplane_of_min_norm`: FALSE in the all-one-sign degenerate case
  (ml-lane compiled counterexample: n=1, x=0, lab=+1 makes 0 feasible and minimal);
  repaired with both-classes-nonempty inputs and closed via the lane's proved
  nondegenerate core.
- `exists_featureMap`: same auto-bound-universe artifact as `exists_rkhs`; pinned to
  `Type (max uK uX)` and proof updated.

## Statement renegotiations (final)

- `sqrtSymbol` (Thm 11.18 apparatus): the original pointwise unordered-`tsum` definition
  junk-defaults to `0` whenever the √λ-series is not absolutely summable — the generic
  case (mercer2-lane circle counterexample `K = ∑ (1+n²)⁻¹ e^{in(x−y)}`, recorded in the
  docstring).  Repaired definitionally: `sqrtSectionLp d x` is the `L²`-valued `tsum` of
  the orthogonal family, `sqrtSymbol d x` its representative.
- `range_mercerCLM_subset`: frozen signature had no access to any regularity of `K`
  (every proof route needs it); repaired with `include hKc in`.

## Final state (2026-08-05)

- **BATCH COMPLETE, 0 sorries.**  Umbrella gate green; axiom sweep: all 44 headline
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
- `StatLean.NonparametricStatistics.RKHS` wired into the area umbrella (laptop commit).
- Full-library build: see phase log; branch `np/rkhs` is the deliverable (NOT merged to
  main, NOT pushed to origin — per request, the work lives on the new branch).
