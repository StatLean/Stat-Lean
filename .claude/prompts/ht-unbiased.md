# Close HypothesisTesting/Unbiased/*.lean and Invariance/MaximalInvariant.lean (2 of 3)

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything you need is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** `StatLean/HypothesisTesting/Unbiased/{PowerContinuity,SimilarityCompleteness,OneParamTwoSided,ConditionalExpFamily,MultiparamUMPU}.lean` and `.../Invariance/MaximalInvariant.lean`.
- Signatures FROZEN (MaximalInvariant's were just corrected — see below). Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors** except the one genuine obstruction named below. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — four such reports have been acted on this campaign, each unblocking real closures on the next pass.
- Commit after each lemma compiles.

## `MaximalInvariant` — two of the three are now unblocked

`InducesOn.mul` now carries `hg' : Measurable ⇑g'`, and `InducesOn.inv` now carries `hgf : Measurable ⇑g` alongside `hg : Measurable ⇑g.symm` — exactly the gaps your predecessor diagnosed (`Measure.map_map` splits a composite pushforward and needs both factors measurable; inverting needs both directions). **Close both.**

`isInvariantTest_iff_factors_measurable` (⇒) is a **genuine obstruction** — measurable uniformization (Jankov–von Neumann); the factor's sublevel set is an analytic projection, not measurable, from a bare `MeasurableEmbedding`. **Do not attempt it**; leave it with its note.

## `Unbiased` — the main work

- `PowerContinuity` (Lem 4.1.1): unbiased + continuous power ⇒ similar on the boundary; then UMP-on-boundary ⇒ UMPU. Mostly topology on the power function.
- `SimilarityCompleteness` (Thm 4.3.2): all similar level-α tests have Neyman structure ⟺ the boundary family of `T`-laws is boundedly complete. From **PointEstimation** (merged, axiom-clean) you have `Completeness.Defs.IsBoundedlyCompleteFamily`, `Sufficiency.Defs.HasSufficientKernel`, and the closed `Sufficiency.Basic.*`. The (⇐) direction is the completeness test applied to `t ↦ ∫ φ dQ_t − α`; (⇒) needs `0 < α < 1` (already in the signature).
- `ConditionalExpFamily` + `MultiparamUMPU` (Thm 4.4.1, the hardest item in Ch 4): the conditional law of `U` given `T = t` in a canonical `(U,T)` exponential family is a one-parameter exponential family whose base depends only on `t` and **not** on the nuisance parameter. `ForMathlib.CondDistribTilt` is the intended engine — check whether it is closed; if it still has sorries, say so and route around it or report. From PointEstimation, `ExponentialFamily.{Basic,MGF,NaturalStatistic}` and `Completeness.ExpFamily.isCompleteStat_of_interior_nonempty` are closed and axiom-clean.
- `OneParamTwoSided`: the point-null UMPU test carries **both** the size condition and the derivative condition `∫ T·φ dP_{θ₀} = α ∫ T dP_{θ₀}` — both are in the frozen signature because the source states both. Use them; do not drop either.

## Closed, axiom-clean — black boxes

`NeymanPearson.Lemma.{exists_mostPowerful, isMostPowerful_npTest}`; `MLR.{hasMLR_expFamily, integral_mono_of_hasMLR}`; `Tests.{PValue, Confidence}`; `Randomization.{ExactLevel, OrbitConditional}`; `Invariance.UMPInvariantFinite.*` (all three, incl. Thm 6.3.1); `ForMathlib.{GroupAverageMeasure, QuantileFunction, CriticalFunction, HypergeometricMoments}`; and from PointEstimation the whole `Sufficiency`/`Completeness`/`ExponentialFamily`/`LinearModel.Canonical` stack.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms isUMPU_of_isUMP_on_boundary`, and for anything left open the precise obstruction.
