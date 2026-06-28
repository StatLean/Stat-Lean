# Close sphere + sparse packing via Mathlib addHaar ball volumes

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean` (`sphere_packing_card`)
- `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean`  (`sparse_packing`)
Keep public signatures/docstrings UNCHANGED. Helpers `private`.

## KEY Mathlib tool: Haar ball-volume scaling
`MeasureTheory.Measure.addHaar_ball`/`addHaar_closedBall`: in `ℝ^n` (`EuclideanSpace ℝ (Fin n)`),
`volume (ball x r) = r^n · volume (ball 0 1)` (for `r ≥ 0`), via `Measure.addHaar_ball_center` +
`Measure.addHaar_ball`. Mathlib: `MeasureTheory.Measure.addHaar_ball`, `Measure.addHaar_closedBall`,
`EuclideanSpace.volume_ball`/`volume_closedBall` (search `./tools/loogle.sh '"addHaar_ball"'`).

## `sphere_packing_card` (Ex 5.8): ≥ 2^n unit vectors, pairwise ≥ 1/2-separated
Maximal `1/2`-separated subset `T` of the unit sphere `𝕊^{n-1}`. By maximality, the radius-`1/4` balls
`{B(tᵢ,1/4)}` are DISJOINT and all ⊂ `B(0, 1+1/4)`. Volume: `|T|·(1/4)^n·v ≤ (5/4)^n·v` ⇒ `|T| ≤ 5^n`
(wrong direction). For the LOWER bound `|T| ≥ 2^n`: maximality ⇒ the radius-`1/2` balls COVER the sphere's
`1/2`-neighbourhood, OR use that `T` is also a `1/2`-COVER, so `|T|·(1/2)^n·v ≥ vol(B(0,1)) = v` would give
`|T| ≥ 2^n`. Use the covering form: a maximal separated set is a cover, and the cover-volume bound gives
`|T| ≥ (1/(1/2))^n /C = 2^n/C`. Pin the exact constant the statement asks for; adjust radius constants to
make `2^n` provable (document any deviation). Isolate the ball-volume-ratio step as ONE `private` lemma.

## `sparse_packing` (Ex 5.8): over s-sparse supports
Fix the support set (s of d coordinates); on that s-dim sphere run `sphere_packing_card`; combine over
`C(d,s)` supports with the Hamming/Varshamov bound (`HammingPacking.gilbert_varshamov`, already CLOSED) for
the support-selection part. `log M ≥ (s/2) log((d-s)/s)`.

GOAL: close both, or reduce each to ONE named `private` ball-volume-ratio / counting core (single sorry +
precise TODO). Adjust separation/radius CONSTANTS as needed to make a clean bound provable — document in docstring.
## DONE: build both modules green; `git add` only the two files; commit. Report closed/residual + constants used.
