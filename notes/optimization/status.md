# Optimization area — status

Plan: `~/.claude/plans/plan-for-formalization-of-starry-leaf.md`.
Reference: Lu, *Big Data Analysis* ch. 10 (`chapter10.tex`), ch. 11
(`chapter11.tex` — note TODO.md mis-cites these as ch10), ch. 12
(`chapter12.tex`).

## STATUS: COMPLETE — area builds 0-sorry, 0-error (full umbrella, 2414 jobs).

All 8 TODO targets + supporting lemmas proven on branch `opt/area` (pushed to
`cannon/opt/area`). Final integration: `git merge --no-ff cannon/opt/area` into `main`
(clean — diff vs main's merge-base is purely `StatLean/Optimization/**` + `notes/optimization/`;
`main` already carries the scaffold stubs, which the merge replaces with proofs).

| Result | Decl | Status |
|---|---|---|
| Def convex (10.1) | Mathlib `ConvexOn` | reused |
| Subgradient (10.2) | `IsSubgradient`, `subdifferential` | def |
| Prop 10.1 local⇒global | `forall_le_of_isLocalMin`, `isGlobalMin_iff_zero_mem_subdifferential` | ✓ |
| L-smooth (11.1) | `IsLSmooth` | def |
| Lemma 11.1 co-coercivity | `cocoercive`, `inner_gradient_sub_nonneg` | ✓ |
| Thm 11.1 GD | `gradientDescent_rate` | ✓ |
| Thm 11.2 Frank–Wolfe | `frankWolfe_rate` (t ≥ 1) | ✓ |
| Lemma 12.1 pillar | `prox_variational_inequality`, `pillar` | ✓ |
| Thm 12.1 proximal | `proximalGradient_rate` | ✓ |
| Lemma 12.2 Lyapunov + Thm 12.2 APGD | `nesterov_lambda_lower`, `acceleratedProximalGradient_rate` (t ≥ 1) | ✓ |

Constants/hypothesis deviations (documented in docstrings): GD `2L‖·‖²/t`; FW & APGD stated for
`t ≥ 1` (t=0 is the trivial initial gap, not provable for the constrained/accelerated base from
the per-step bound); co-coercivity adds `ConvexOn` to the book's "L-smooth f".

**Auth note:** Waves 2–3 + all fixes were completed BY HAND on the laptop (verified via
`lean-fasrc-build`, which needs no API auth) because the cluster `claude` credential expired
mid-run (401). Re-auth the cluster `claude` to restore proof delegation for future work.

## Integration model (revised — Batch-1 co-edits the shared working copy)

Batch-1's orchestration loop commits to whatever branch is checked out in the primary
working copy, so Optimization is developed in a **dedicated git worktree** `../Stat-Lean-opt`
on branch **`opt/area`** (based on the pristine `cannon/opt/scaffold` = 5447a13). Primary
working copy stays on `main` for Batch-1. Cluster wrappers run from the worktree with
`LEAN_FASRC_PROJECT=Stat-Lean`. Wave branches base off `opt/area`, merge back into `opt/area`;
`opt/area` → `main` only at the final area gate.

**rc143 note:** cluster-claude srun sessions exit 143 (SIGTERM, shared-partition preemption /
teardown) but the auto-commit captures completed work. Loop: launch → build-verify the branch →
fix small errors on laptop or re-launch → merge. Do NOT treat rc143 as failure without checking
the committed diff + a build.

## Parallel-with-Batch-1 invariants

* Optimization writes only `StatLean/Optimization/**` + `notes/optimization/**`.
* Branch namespace `opt/*` (Batch 1 uses `conc/*`, `hds/*`).
* Only shared file: `StatLean/StatLean.lean` (laptop-only, one import line added).
* Never touch: `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`,
  other areas' umbrellas/Defs.

## Expected sorry inventory (per file) — for the verification gate

FirstOrderConvex 1 · GradientCalc 1 · Subgradient 1 · CoCoercive 2 ·
Pillar 2 · LocalGlobal 2 · GradientDescent 1 · FrankWolfe 1 ·
ProximalGradient 1 · AcceleratedProximal 2.  Total at scaffold: 14.
