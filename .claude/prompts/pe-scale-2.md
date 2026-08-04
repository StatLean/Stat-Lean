# Close Equivariance/{ScaleMRE,ScaleStructure,LocationMRE,LocationExamples}.lean — the false hypothesis is FIXED

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/Equivariance/{ScaleMRE,ScaleStructure,LocationMRE,LocationExamples}.lean`.
- Signatures FROZEN (ScaleMRE's was just corrected — see below). Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors** except the one genuine obstruction named below.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — five such reports have been acted on this campaign, including the one that produced the fix you are now benefiting from.
- Commit after each lemma compiles.

## The false hypothesis has been corrected

Your predecessor proved `isScaleMRE_of_conditional_min` **false as stated**: `hmin` ranged only over *positive* `w`, but the equivariant class is `δ₀ / w` with `w` over the **nonzero reals**, so opposite-signed competitors were never dominated. (Counterexample, r = 0: `δ₀ ≡ 1`, `wStar ≡ 1`, `γ v = (v−1)²+1` for `v > −1` and `0` for `v ≤ −1`; `hmin` holds tightly yet `δ' ≡ −2` has strictly smaller risk.)

**`hmin` now quantifies over all `w ≠ 0`.** Close the theorem: represent an arbitrary equivariant competitor as `δ₀ / w(scaleZ ·)` via `ScaleStructure.isScaleEquivariant_iff_div_invariant`, then apply `ConditionalRiskEngine.lintegral_le_of_condMinimizer` fibrewise. `exists_isScaleMRE_of_convex` was blocked only by this and should follow.

## The other files

- `ScaleStructure` (1): the `mpr` of the measurable factorization was reported **false** — a non-Borel subset of the null hyperplane breaks it. Verify that claim; if it holds, leave it sorried with the counterexample and report. Do not force it.
- `LocationMRE` (2): `exists_measurable_condMinimizer_convex` — the crux is continuity of the `ℝ≥0∞`-valued convex objective `w ↦ ∫⁻ ofReal(ρ(δ₀· − w)) ∂κ(z)` (it can jump finite→∞ at its finiteness boundary), plus coercivity via Fatou, feeding `ForMathlib.MeasurableArgmin.exists_measurable_argmin` (closed; note it takes **continuity**, deliberately, not lower semicontinuity). And `exists_isLocMRE_of_bounded_loss` — translation-continuity of `c ↦ ∫ ρ(t−c) f(t) dt` by DCT, then extreme value on a compact sublevel set.
- `LocationExamples` (1): `isLocMRE_mean_gaussian`. **`Pitman.lean` is now 0-sorry** (both `pitmanEstimator_eq_sub_condMean` and `pitmanEstimator_isLocMRE`), so the cheap route is open: for the Gaussian location family the Pitman ratio evaluates in closed form to `X̄` by completing the square in the exponent — no Basu machinery needed. Do **not** attempt the Kagan–Linnik–Rao converse (explicitly out of scope).

## Closed, axiom-clean — black boxes

`Equivariance.{Pitman, LocationStructure, ConditionalRiskEngine, RiskUnbiased, General}`; `LocationMRE.{isLocMRE_of_conditional_min, isLocMRE_sq_of_condMean}`; `ForMathlib.{CondDistribDensity, MeasurableArgmin, ConvexMinimizers, HalmosSavage, CondExpWithDensity, MGFUniqueness, MGFUniquenessPi, IntegrationByPartsReal}`; `Completeness.{Basu, ExpFamily}`; `LinearModel.{Canonical, GaussMarkov}`; `Sufficiency.*`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms isScaleMRE_of_conditional_min`, and for anything left open the precise obstruction.
