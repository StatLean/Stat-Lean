# Close the sorries in PointEstimation/Completeness/Basu.lean, ExponentialFamily/MinimalSufficient.lean, and UMVU/LehmannScheffe.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.Completeness.Basu`, then `.ExponentialFamily.MinimalSufficient`, then `.UMVU.LehmannScheffe`. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/Completeness/Basu.lean`, `.../ExponentialFamily/MinimalSufficient.lean`, `.../UMVU/LehmannScheffe.lean`. Touch nothing else — no `Defs.lean` (all frozen, laptop-only).
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*`, import already-closed project modules, and add `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms indepFun_of_boundedlyComplete_sufficient`, `#print axioms isUMVU_of_complete_sufficient` — expect only `propext, Classical.choice, Quot.sound`.

## Already closed, treat as black boxes (import them)

- `Completeness.ExpFamily.{isCompleteStat_of_interior_nonempty, isCompleteStat_of_interior_nonempty_real}` — exponential-family completeness (Thm 6.22), axiom-clean.
- `Sufficiency.Basic.{isSufficient_of_hasSufficientKernel, hasSufficientKernel_fiber, statLaw_snd}` and `Sufficiency.RiskEquality.*`.
- `UMVU.RaoBlackwell.{rbEstimator, isUnbiased_rbEstimator, risk_rbEstimator_le, variance_rbEstimator_le}` — Rao–Blackwell via plain per-fiber Jensen.
- `UMVU.CovarianceCriterion.isUMVU_iff_uncorrelated_unbiasedZero`, `UMVU.Basic.isUMVU_unique`.
- `ExponentialFamily.{Basic,MGF,NaturalStatistic}` are fully closed.

## Notes on specific targets

- **`completeStat_boundedlyCompleteStat`** (and `IsCompleteFamily.boundedlyComplete`): bounded measurable functions on probability measures are integrable, so the bounded test set is a subset of the full one. Short.
- **`indepFun_of_boundedlyComplete_sufficient` (Basu, Thm 6.21)**: for measurable `A`, put `f t := Q t (V ⁻¹' A)` where `Q` is the θ-free sufficient kernel. `f` is bounded and measurable; `∫ f d(statLaw θ) = P θ (V ∈ A)` is constant in `θ` by ancillarity, so `f − P(V ∈ A)` integrates to zero for every `θ`. **Bounded** completeness then forces `f = P(V ∈ A)` a.e., and the compProd graph identity turns that into the product formula `P θ (T ∈ B ∩ V ∈ A) = P θ (T ∈ B) · P θ (V ∈ A)`, i.e. `IndepFun T V (P θ)`. Note Basu is deliberately stated with **bounded** completeness — the honest minimal hypothesis. Do not strengthen it.
- **`fullRank_exists_affineSpan` / `isMinimalSufficient_stat` (Cor 6.16)**: full rank gives `s+1` parameter points whose affine span is everything; sufficiency of `T` is the factorization; minimality because the likelihood ratios between those points determine `T` up to a.e. equality, and any competing sufficient `U` makes those ratios `U`-measurable, so `T` factors through `U` by Doob–Dynkin (`Measurable.exists_eq_measurable_comp`).
- **`unique_unbiased_function_of_complete` (Lem 1.10)**: note this needs **only completeness**, not sufficiency — the file docstring records that as a deliberate strengthening over the classical statement. Two unbiased functions of `T` differ by a function with identically zero mean, which completeness kills.
- **`isUMVU_of_complete_sufficient` (Thm 1.11a)**: Rao–Blackwellize an arbitrary unbiased estimator through the complete sufficient `T`; the result is unbiased (imported) and, by uniqueness, is *the* unbiased function of `T`; minimal variance then follows from `variance_rbEstimator_le` applied to every competitor. `risk_le_of_complete_sufficient` (Thm 1.11b) is the same argument with `risk_rbEstimator_le` for an arbitrary nonneg convex loss.
- **`isUMVU_of_fullRank_expFamily` (Cor 1.12)**: assemble — completeness from `Completeness.ExpFamily`, sufficiency from the exponential-family factorization, then Thm 1.11a.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, and any statement you believe is false (with the counterexample).
