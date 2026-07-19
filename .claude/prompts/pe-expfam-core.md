# Close the sorries in PointEstimation/ExponentialFamily/{Basic,MGF,NaturalStatistic}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.ExponentialFamily.Basic` (then `.MGF`, then `.NaturalStatistic`) and read the output directly. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/ExponentialFamily/Basic.lean`, `.../MGF.lean`, `.../NaturalStatistic.lean`. Touch nothing else — in particular NOT `ExponentialFamily/Defs.lean` (frozen, laptop-only).
- **Signatures, hypothesis tags, and docstrings are FROZEN.** You may add `import Mathlib.*` and `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors** across the three files. Escape hatch: at most one lifted `private` sorry per file, each with a `-- TODO:` naming exactly what is missing; report them.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample. Honest refusal is the desired outcome.
- Commit after each lemma compiles.
- After green: `#print axioms integral_exp_inner_P`, `#print axioms map_stat_P` — expect only `propext, Classical.choice, Quot.sound`.

## Context you need

The area's exponential family is **canonical and tilt-based** (`ExponentialFamily/Defs.lean`, frozen):
`E.P η = E.base.tilted (fun x => ⟪η, E.stat x⟫_ℝ)`, `E.natSet = {η | Integrable (exp ⟪η, stat ·⟫) E.base}`, `E.logPartition η = log (∫ exp ⟪η, stat x⟫ ∂E.base)`.

Because members are built with `Measure.tilted`, most of Mathlib's tilt API applies directly, and the junk convention (`E.P η = 0` off `natSet`) is inherited rather than hand-rolled.

## Notes on specific targets

- `natSet_convex`: Hölder / `inner_smul_add` interpolation on the integrand.
- `isProbabilityMeasure_P`, `P_eq_zero_of_notMem`: near-immediate from `isProbabilityMeasure_tilted` and `tilted_of_not_integrable`.
- `P_eq_withDensity`: unfold `Measure.tilted`; the normalising constant is `exp (E.logPartition η)`.
- **`integral_exp_inner_P` (the mgf identity) carries a genuine nondegeneracy hypothesis `E.base ≠ 0`** — for the zero measure the identity would read `0 = 1`. Use it; do not try to remove it.
- `integral_stat_P` / `variance_stat_P` (the 1-D moment identities) are the `V := ℝ` case and deliberately carry **no** nondegeneracy hypothesis: both sides degenerate to `0`. Mathlib's `deriv_cgf` and `iteratedDeriv_two_cgf` are the intended bricks; note our `⟪η, T x⟫_ℝ` at `ℝ` reduces to `T x * η` while Mathlib's `cgf`/`tilted` use `η * T x`, so a `mul_comm` bridge is needed (the file already stubs those bridge lemmas — prove them first).
- `map_stat_P` (Thm 5.17): the law of `T` under `P η` is the canonical family on `V` with base `T#ν` and statistic `id`. `Measure.map_map` plus the tilt-pushforward identity; mind the direction of `Measure.map_map` (see `CLAUDE.md` §7.11).

## Report

Final `lake build` status for each of the three modules, per-file sorry counts, and the two `#print axioms` outputs. Flag any statement you believe is false.
