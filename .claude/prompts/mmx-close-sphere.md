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
**IMPORTANT — ambient ball volume is NOT enough for `2^n`.** The annulus argument
`A_h={1-h≤‖x‖≤1+h} ⊆ ⋃ B(t,1/2+h)` only gives `|T| ≥ (3/2)^n`-ish (< `2^n`); the genuine `2^n` needs the
**sphere SURFACE measure**, which Mathlib HAS:
- `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` — the surface measure `μ_S` on the unit sphere
  from the Lebesgue/Haar polar disintegration (`volume = ∫_{r} rⁿ⁻¹ dr ⊗ μ_S`-style). Search it for
  `Measure.toSphere`, `volume_eq_…sphere…`, and the cap-measure relation.
- `Mathlib/Analysis/Normed/Module/Ball/RadialEquiv.lean` — `homeomorphUnitSphereProd` (polar coords).
LOWER bound `2^n`: maximal `1/2`-separated ⇒ `1/2`-COVER of the sphere ⇒ `μ_S(S) ≤ |T|·μ_S(cap(t,1/2))`,
and the cap surface `μ_S(cap(·,1/2)) ≤ (1/2)^{n-1}·μ_S(S)`-style bound gives `|T| ≥ 2^{n-1}` (adjust to `2^n`
by tuning the separation/radius constant — **document any deviation in the docstring** per CLAUDE.md §1).
FALLBACK (this is genuinely hard): if the cap-surface-measure estimate is too heavy, prove everything around it
and isolate the single inequality `μ_S(cap(t, 1/2)) ≤ c·μ_S(S)` as ONE named `private` lemma (one sorry +
precise `-- TODO(mmx)`). Do NOT bare-sorry the public theorem; ≤ 1 named residual.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SpherePacking` green (0 sorry, or ≤1 named residual).
`git add` ONLY that file; commit. Report the volume argument + any constant deviation.
