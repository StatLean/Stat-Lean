# Optimization area — status

Plan: `~/.claude/plans/plan-for-formalization-of-starry-leaf.md`.
Reference: Lu, *Big Data Analysis* ch. 10 (`chapter10.tex`), ch. 11
(`chapter11.tex` — note TODO.md mis-cites these as ch10), ch. 12
(`chapter12.tex`).

## Waves

* **Wave 0 — `opt/scaffold`** (laptop): DONE. Stub-gate green (2400 jobs, 14 sorries).
* **Wave 1 — concept layer**: DONE, merged into `opt/area`, verified green (2414 jobs,
  7 sorries remaining). `opt/convex-core` (FirstOrderConvex, Subgradient, LocalGlobal/Prop 10.1)
  + `opt/smoothness` (GradientCalc ∇=0-at-min, CoCoercive/Lem 11.1). Laptop fixed 2 trivial
  post-preemption errors (open scoped Topology; dropped redundant `ring` after field_simp).
* **Wave 2 — first-order methods** (IN FLIGHT, based on `opt/area`):
  * `opt/gradient-descent`: GradientDescent (Thm 11.1).
  * `opt/frank-wolfe`: FrankWolfe (Thm 11.2).
* **Wave 3 — proximal track** (queued):
  * `opt/prox-pillar`: Prox/Pillar (Lem 12.1) — first.
  * `opt/proximal-gradient`: ProximalGradient (Thm 12.1).
  * `opt/accelerated-proximal`: AcceleratedProximal (Thm 12.2).

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
