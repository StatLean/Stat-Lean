# Optimization area — status

Plan: `~/.claude/plans/plan-for-formalization-of-starry-leaf.md`.
Reference: Lu, *Big Data Analysis* ch. 10 (`chapter10.tex`), ch. 11
(`chapter11.tex` — note TODO.md mis-cites these as ch10), ch. 12
(`chapter12.tex`).

## Waves

* **Wave 0 — `opt/scaffold`** (laptop): all `Defs.lean` + sorry'd stubs +
  umbrella + root import + notes. → stub-gate build green-with-sorries.
  STATUS: files written; stub-gate build pending.
* **Wave 1 — concept layer** (2 concurrent cluster sessions):
  * `opt/convex-core`: ForMathlib/FirstOrderConvex, Convex/Subgradient, LocalGlobal.
  * `opt/smoothness`: ForMathlib/GradientCalc, Smoothness/CoCoercive (Lem 11.1).
* **Wave 2 — first-order methods** (after Wave 1):
  * `opt/gradient-descent`: GradientDescent (Thm 11.1).
  * `opt/frank-wolfe`: FrankWolfe (Thm 11.2).
* **Wave 3 — proximal track**:
  * `opt/prox-pillar`: Prox/Pillar (Lem 12.1) — first.
  * `opt/proximal-gradient`: ProximalGradient (Thm 12.1).
  * `opt/accelerated-proximal`: AcceleratedProximal (Thm 12.2).

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
