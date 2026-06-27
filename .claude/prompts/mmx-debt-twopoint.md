# Close binary Bayes-error = TV (LeCam/TwoPoint.lean, Eq 15.13) — unlocks 3 method theorems

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.
CRITICAL: do NOT increase the file's sorry count. Close `binary_testingError_eq_tvDist` or leave it unchanged.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/LeCam/TwoPoint.lean`
Close `binary_testingError_eq_tvDist`: `multiwayTestingError Q = ½(1 − tvDist (Q 0) (Q 1))` for `M=2`.
`multiwayTestingError Q = bayesRisk (zeroOneLoss 2) Q (uniformPrior 2)` = inf over Markov kernels
`κ : 𝓧 → Fin 2` of `½(∫ κ{≠0} dQ0 + ∫ κ{≠1} dQ1)`.

## Strategy — Mathlib decision theory
Search Mathlib `ProbabilityTheory` decision-risk API for the binary-test optimum:
`./tools/loogle.sh '"bayesRisk"'`, `'"bayesBinaryRisk"'` — Mathlib HAS `bayesBinaryRisk` and likely
`bayesBinaryRisk_eq_…`/`…_eq_tv`/`bayesBinaryRisk … = (μ ⊓ ν) …` relating the binary Bayes risk to the
total variation / measure infimum `(Q0 ⊓ Q1) univ`. The classical identity: optimal binary test error
`= ½(1 − ‖Q0 − Q1‖_TV) = (Q0 ⊓ Q1)(univ)/…`. Bridge our `multiwayTestingError`/`zeroOneLoss`/`uniformPrior`
to Mathlib's `bayesBinaryRisk` (or reduce the `iInf` over Markov kernels to deterministic LR tests:
`Kernel.deterministic` suffices since the loss is linear ⇒ extreme points; the optimal acceptance region is
`{dQ0/d(Q0+Q1) ≥ dQ1/…}`). Then relate to `tvDist` via `tvDist_eq_half_lintegral` (CLOSED).
KEY Mathlib search: `bayesBinaryRisk`, `bayesBinaryRisk_eq`, `Measure.inf`, `totalVariation`, `lintegral_inf`.

GOAL: close it (it unlocks `minimax_two_point`, and downstream `minimax_le_cam_convex_hull` via ConvexHull).
If the `iInf`-over-kernels → deterministic reduction is the hard part, isolate THAT as one named `private`
lemma (single sorry) and prove the rest. Do not exceed 1 sorry in the file.
## DONE: build module green; `git add` only that file; commit. Report closed/residual + Mathlib lemmas found.
