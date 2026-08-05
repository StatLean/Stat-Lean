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
| ml | `np/rkhs-ml` | FeatureMap, Separation, MaxMargin, Representer | RUNNING |
| integral | `np/rkhs-integral` | IntegralOperator, RangeSpace, Mercer/Defs, Mercer/OperatorLemmas | RUNNING |
| mercer | `np/rkhs-mercer` | Mercer/Basic, Mercer/Compact, Mercer/Theorem, Mercer/SquareRoot | queued (wave 3) |

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

## Debts

- `dualRKHS_range_coe` (restated) — 1 sorry, residual pass.
