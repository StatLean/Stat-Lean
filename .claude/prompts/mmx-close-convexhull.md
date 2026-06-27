# Close #13: Le Cam convex-hull bound (ConvexHull.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds. Goal 0 sorry.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/LeCam/ConvexHull.lean`
Close the `sorry` body of `minimax_le_cam_convex_hull`. The signature now has `[OpensMeasurableSpace Ω]`
(added upstream). Keep signature/docstring UNCHANGED; helpers `private`.

## Available (proven, black-box)
- `EstimationToTesting.lean`: `exists_measurable_nearestPoint` (the reusable measurable nearest-point
  selector built for the point-family case — REUSE it for the two-class test), `minimax_ge_testing_error`,
  `mul_multiwayTestingError_le`.
- `ForMathlib/TotalVariation.lean`: `one_sub_tvDist_eq_iInf`, `tvDist_eq_half_lintegral`.

## Strategy — mixture two-point bound
Goal: `Φ δ / 2 * (1 - tvDist (P.comap a₀ ha₀ ∘ₘ π₀) (P.comap a₁ ha₁ ∘ₘ π₁)) ≤ minimaxRiskDist Φ g P`.
Two `2δ`-separated subfamilies `{g(a₀ i)}`, `{g(a₁ i)}` (hypothesis `hsep`); mixtures `m₀ = P.comap a₀ ∘ₘ π₀`,
`m₁ = P.comap a₁ ∘ₘ π₁`. Build the binary nearest-point test deciding class 0 vs class 1 from any estimator
(via `exists_measurable_nearestPoint` applied to the two-class functional values — the `2δ`-separation gives
the same Markov/triangle bound as the point case). Reduce the minimax risk to `½(1 − tvDist m₀ m₁)` using the
binary testing error `= ½(1 − TV)` form (cf. `binary_testingError_eq_tvDist`, already proven) and the variational
`one_sub_tvDist_eq_iInf`. Mirror the structure of `mul_multiwayTestingError_le` but for the 2-class mixture.

If the full mixture selector resists, isolate the mixture analogue as ONE named `private` lemma and prove the
TV-reduction around it. GOAL 0 sorry.

## DONE: `lake build StatLean.Minimaxity.LeCam.ConvexHull` green, 0 sorry. `git add` ONLY that file; commit.
