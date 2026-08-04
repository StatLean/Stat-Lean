# Close MLR/{OneSided,TwoSided,StochasticDominance,ConfidenceBounds}.lean and NeymanPearson/{Generalized,LeastFavorable}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** those six files. Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — six such reports have been acted on this campaign, and every one unblocked real closures on the next pass. It is the single most valuable thing you can produce if a statement resists.
- Commit after each lemma compiles.

## What is already available (closed, axiom-clean — black boxes)

- **`NeymanPearson.Lemma`**: `exists_mostPowerful` (existence of the NP test with exact size), `isMostPowerful_npTest` (sufficiency), the fundamental inequality, and the strict-unbiasedness corollary.
- **`ForMathlib.QuantileFunction`**: `quantile`, `quantile_mono`, `quantile_le_iff`, **`exists_critical_constants`** (for a probability law on `ℝ` and `α ∈ (0,1)`, constants `C` and `γ ∈ [0,1]` with `P(C,∞) + γ·P{C} = α`), `map_quantile_uniform`, and both quantile-convergence lemmas.
- **`Tests.Confidence`**: all six duality theorems. `MLR/ConfidenceBounds` should be a short instantiation — note the last slot of `IsUMAConfidence` is the **coverage** level `1 − α`.
- **`MLR`**: `hasMLR_expFamily` and `integral_mono_of_hasMLR` are closed.
- From **PointEstimation** (merged, axiom-clean): the whole `ExponentialFamily` stack (`Basic`, `MGF`, `NaturalStatistic`) plus `Completeness.ExpFamily.isCompleteStat_of_interior_nonempty`.

## Notes per file

- `MLR/OneSided` (Thm 3.4.1, 6 open): the UMP one-sided test. `HasMLR` is the division-free TP2 form. Get the constants from `exists_critical_constants` applied to the law of `T` under `P θ₀`, then apply the NP sufficiency direction pointwise on `{θ > θ₀}`. `power_strictMono_oneSided` carries an explicit distinctness hypothesis `hdist` because the frozen `HasMLR` admits constant families — use it.
- `MLR/TwoSided` (Thm 3.7.1, 4): the exponential-family two-sided UMP. Two constraint equations pin `C₁ < C₂`; the generalized-NP machinery is **not** needed for the frozen statement — the direct comparison argument suffices.
- `MLR/StochasticDominance` (2): quantile coupling — push the uniform law on `(0,1)` through each quantile function; `map_quantile_uniform` is exactly the tool.
- `NeymanPearson/Generalized` (Thm 3.6.1, 7): the multi-constraint NP lemma. Existence is the weak-compactness argument — **`ForMathlib/TestsWeakCompact` is still open**, so if you need it, either prove the pieces you need as `private` helpers here or report the dependency. The `m ≤ 2` case (all that `TwoSided` and the Ch-4 UMPU tests actually consume) is provable by the explicit two-constraint continuity argument without any compactness; **do that first** and leave general-`m` existence as the documented debt if it resists.
- `NeymanPearson/LeastFavorable` (Thm 3.8.1, 4): waits on a mixture-Fubini bridge `∫ φ d(∫ P θ dΛ) = ∫ (∫ φ dP θ) dΛ`. Build it as a `private` helper from `Measure.integral_bind`-style lemmas plus the joint measurability already in the signature.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms isUMP_oneSided`, and for anything left open the precise obstruction.
