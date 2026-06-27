# Close #10: sphere packing cardinality (SpherePacking.lean) — HARD

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean`
Close `sphere_packing_card (n) (hn : 1 ≤ n) : ∃ T : Finset (EuclideanSpace ℝ (Fin n)), 2^n ≤ T.card ∧
(∀ v∈T, ‖v‖=1) ∧ ∀ u∈T v∈T, u≠v → 1/2 ≤ ‖u−v‖`. Keep signature UNCHANGED; helpers `private`.

## Strategy — maximal separated set + ball-volume counting
Take a **maximal** `1/2`-separated subset `T` of the unit sphere (exists: the sphere is compact, a
`1/2`-separated set is finite with cardinality bounded by a volume ratio, so a maximum-cardinality one exists —
use `Set.Finite`/`Finset` extremal choice). By maximality the open `1/2`-balls `{B(t,1/2) : t∈T}` **cover** the
unit sphere. Counting: the disjoint `1/4`-balls `{B(t,1/4)}` lie in `B(0,5/4)`, and a covering/packing volume
ratio gives `|T| ≥ 2^n`.
KEY Mathlib: `EuclideanSpace.volume_ball (x) (r) : volume (Metric.ball x r) = (ofReal r)^n * (ofReal (√π^n/Γ(n/2+1)))`
— the constant CANCELS in the ratio. Also `Measure.addHaar_ball`, `addHaar_closedBall_eq_addHaar_ball`,
`MeasureTheory.measure_iUnion_le`/`measure_biUnion_finset` (disjoint), `Metric.ball_subset_ball`.
- Disjoint `1/4`-balls in `B(0,5/4)`: `|T|·(1/4)^n·C ≤ (5/4)^n·C` gives an UPPER bound (not needed).
- For the LOWER bound `2^n`: use that maximal-separated ⇒ `1/2`-cover, so `vol(B(0,1)) ≤ |T|·vol(B(·,1/2))`,
  i.e. `1 ≤ |T|·(1/2)^n`, hence `|T| ≥ 2^n`. (Cover the unit ball `B(0,1)` ⊃ unit sphere by the `1/2`-balls.)
You MAY adjust the separation/radius constants (e.g. work with the closed unit ball, or `1/2`→`1/2`) to make a
clean `2^n` provable; **document any deviation in the docstring** per CLAUDE.md §1. Isolate the volume-ratio
step as ONE `private` lemma; if the maximal-set existence is the sticking point, isolate THAT as the single
named residual.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SpherePacking` green (0 sorry, or ≤1 named residual).
`git add` ONLY that file; commit. Report the volume argument + any constant deviation.
