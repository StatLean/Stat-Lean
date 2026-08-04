# Close Equivariance/{Pitman,LocationExamples,LocationMRE}.lean — the a.e. mismatch is now FIXED

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything you need is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/Equivariance/{Pitman,LocationExamples,LocationMRE}.lean`.
- Signatures FROZEN (just corrected — see below). Add `import Mathlib.*`, closed project modules, and `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is still wrong, STOP and report precisely — three such reports have already been acted on this campaign.
- Commit after each lemma compiles.

## The blocking mismatch has been fixed

Your predecessor found that `pitmanEstimator_eq_sub_condMean` was stated **pointwise** (`∀ x`) while `orbitCondKernel` is a `condDistrib`, determined only up to a null set — so no route could prove it. **The conclusion is now `∀ᵐ x ∂(locationBase f), …`.** Prove it in that register.

Its recommendation stands: **work in the a.e. register throughout**, matching `isLocMRE_of_conditional_min`, which is a.e.-only by construction.

Route for `pitmanEstimator_eq_sub_condMean`: `ForMathlib.CondDistribDensity.condDistrib_withDensity_prod_ae_eq` (CLOSED, axiom-clean) identifies the conditional law given `diffs` as the normalized slice; then a **det-1 shear** change of variables (`x ↦ (diffs x, xₙ)` is Lebesgue-measure preserving) turns the slice integral into the displayed ratio. The companion private helper `integrable_lastCoord_orbitCondKernel` should likewise be recast a.e. if its `∀ y` form blocks you — report if so rather than forcing it.

## Then the cascade

- `pitmanEstimator_isLocMRE` follows from the above plus `isLocMRE_sq_of_condMean` (closed).
- `LocationExamples.isLocMRE_mean_gaussian`: your predecessor noted `Basu.indepFun_of_boundedlyComplete_sufficient` needs `HasSufficientKernel` / `IsBoundedlyCompleteStat` / `IsAncillary` for the **location** family, none of which are pre-built (only the canonical model has them). If building those is out of budget, the cheaper route is direct: for the Gaussian location family the Pitman ratio evaluates in closed form to `X̄` by completing the square in the exponent — no Basu needed. Try that first.
- `LocationMRE.exists_measurable_condMinimizer_convex`: the crux your predecessor flagged is **continuity of the `ℝ≥0∞`-valued convex objective** `w ↦ ∫⁻ ofReal(ρ(δ₀· − w)) ∂κ(z)`, which can jump finite→∞ at its finiteness boundary; plus coercivity via Fatou, feeding `ForMathlib.MeasurableArgmin.exists_measurable_argmin` (closed — note it takes **continuity**, not lower semicontinuity, deliberately).
- `LocationMRE.exists_isLocMRE_of_bounded_loss`: independent; the substance is translation-continuity of `c ↦ ∫ ρ(t − c) f(t) dt` by DCT, then extreme-value on a compact sublevel set.

## Closed, axiom-clean — black boxes

`ForMathlib.{CondDistribDensity, MeasurableArgmin, ConvexMinimizers, CondExpWithDensity, HalmosSavage, MGFUniqueness, MGFUniquenessPi, IntegrationByPartsReal}`; `Equivariance.{LocationStructure, ConditionalRiskEngine, RiskUnbiased, General}`; `LocationMRE.{isLocMRE_of_conditional_min, isLocMRE_sq_of_condMean}`; `Completeness.{Basu, ExpFamily}`; `Sufficiency.*` (except the sanctioned general regular-conditional deferral); `LinearModel.{Canonical, GaussMarkov}`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms pitmanEstimator_isLocMRE`, and for anything left open the precise obstruction.
