# Close the remaining sorries in HypothesisTesting/NeymanPearson/{Lemma,LeastFavorable}.lean and MLR/{OneSided,StochasticDominance,ConfidenceBounds,TwoSided}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Build in dependency order: `StatLean.HypothesisTesting.NeymanPearson.Lemma`, `.NeymanPearson.LeastFavorable`, `.MLR.StochasticDominance`, `.MLR.OneSided`, `.MLR.TwoSided`, `.MLR.ConfidenceBounds`. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** those six files. Touch nothing else — NOT `Tests/Defs.lean` or `MLR/Defs.lean` (frozen, laptop-only), and NOT the already-closed `ForMathlib/{CriticalFunction,QuantileFunction}.lean` or `Tests/{PValue,Confidence}.lean`.
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*`, import closed project modules, and add `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample. Honest refusal is the desired outcome.
- Commit after each lemma compiles.
- After green: `#print axioms exists_mostPowerful`, `#print axioms isUMP_oneSided` — expect only `propext, Classical.choice, Quot.sound`.

## Second pass on NeymanPearson

A previous session closed the fundamental inequality, the `npShape`/`npTest` sufficiency direction, and the degenerate power case. It left **3 TODOs in `Lemma.lean`** (existence, necessity/uniqueness, strict unbiasedness) and **4 in `LeastFavorable.lean`** (all waiting on a mixture-Fubini bridge). Read those TODO comments first — they say exactly where the previous session stopped.

**The blocker for existence is already gone**: `ForMathlib/QuantileFunction.exists_critical_constants` is now **closed and axiom-clean** — for a probability measure on `ℝ` and `α ∈ (0,1)` it gives `C` and `γ ∈ [0,1]` with `P(C,∞) + γ·P{C} = α`. Apply it to the law of the likelihood ratio under `P₀` to get the NP randomization constants; then `isMostPowerful_npTest` (already closed) finishes existence.

For `LeastFavorable`, the missing bridge is Fubini for the mixture: `∫ φ d(∫ P θ dΛ) = ∫ (∫ φ dP θ) dΛ`. Build it as a `private` helper from `Measure.lintegral_bind`/`Measure.integral_bind`-style lemmas, with the joint measurability of `(θ,x) ↦ p θ x` that the signature already provides.

## Already closed, treat as black boxes

- `ForMathlib.QuantileFunction.{quantile, quantile_mono, quantile_le_iff, exists_critical_constants, map_quantile_uniform, tendsto_quantile_of_tendsto, tendstoInMeasure_quantile}`
- `ForMathlib.CriticalFunction.{randomizedTestKernel, …}`
- `Tests.PValue.superUniform_nestedPValue`, and **all six** `Tests.Confidence` duality theorems (`isConfidenceFamily_of_acceptance`, its converse, `isUMA_of_UMP`, …) — `MLR/ConfidenceBounds` should be a short instantiation of these.
- From Batch 11 (merged, axiom-clean): `PointEstimation.ExponentialFamily.{Basic,MGF,NaturalStatistic}` and `Completeness.ExpFamily.isCompleteStat_of_interior_nonempty` — for the exponential-family corollaries (`hasMLR_expFamily`, `isUMP_oneSided_expFamily`, `TwoSided`).

## Notes on the MLR files

- `StochasticDominance` (Lem 3.4.1): the quantile coupling. `map_quantile_uniform` (closed) is exactly the tool — push the uniform law on `(0,1)` through each quantile function; monotonicity gives `f₀ ≤ f₁` from `F₁ ≤ F₀`.
- `OneSided` (Thm 3.4.1): the UMP one-sided test. `HasMLR` is the division-free TP2 form — for `θ < θ'` and `T x ≤ T y`, `p θ' x · p θ y ≤ p θ x · p θ' y`. Combine with `exists_critical_constants` for the constants and the NP sufficiency direction pointwise. **Note `power_strictMono_oneSided` carries an explicit distinctness hypothesis `hdist`** because the frozen `HasMLR` admits constant families; use it, don't remove it.
- `TwoSided` (Thm 3.7.1): the exponential-family two-sided UMP. Two constraint equations pin `C₁ < C₂`; the generalized-NP machinery is *not* required for the frozen statement — the direct comparison argument suffices.
- `ConfidenceBounds` (Cor 3.5.1): instantiate the closed duality lemmas with the one-sided MLR test. **The confidence level in the last slot of `IsUMAConfidence` is the coverage `1 − α`**, not `α` — the file already reflects that; keep it.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, and any statement you believe is false (with the counterexample).
