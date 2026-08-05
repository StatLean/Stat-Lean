# RKHS batch — status

Integration branch: `np/rkhs` (off local main `cd41a7d9`).  See `outline.md` for the
book↔Lean dictionary and lane plan.

## Phase log

- 2026-08-05: 25 stub files + umbrella `StatLean/NonparametricStatistics/RKHS.lean`
  authored on laptop (statement-first, all proofs `sorry`).  NOT yet wired into the area
  umbrella `StatLean/NonparametricStatistics.lean` (done at merge, laptop-only).
  Next: stub gate on FAS-RC, then lane fan-out.

## Lane status

| Lane | Branch | Files | State |
|---|---|---|---|
| core | `np/rkhs-core` | Basic, KernelFunction, OrthonormalExpansion, Subspace, Continuity | stubs |
| frames | `np/rkhs-frames` | ParsevalFrame, Papadakis | stubs |
| sobolev | `np/rkhs-sobolev` | MinKernel, Sobolev | stubs |
| moore | `np/rkhs-moore` | Moore, Uniqueness, RankOne, InnerKernel | stubs |
| ml | `np/rkhs-ml` | FeatureMap, Separation, MaxMargin, Representer | stubs |
| integral | `np/rkhs-integral` | IntegralOperator, RangeSpace, Mercer/Defs, Mercer/OperatorLemmas | stubs |
| mercer | `np/rkhs-mercer` | Mercer/Basic, Mercer/Compact, Mercer/Theorem, Mercer/SquareRoot | stubs |

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

## Debts

(to be filled at lane harvest; target 0-sorry at close)
