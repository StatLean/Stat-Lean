# Close #10: sphere packing lower bound via Measure.toSphere (SpherePacking.lean) — HARD

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build).

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean`
Close `two_pow_le_packingNumber_sphere (n) (hn : 1 ≤ n) : (2:ℕ∞)^n ≤ packingNumber (1/2) (sphere 0 1)`
(sphere in `EuclideanSpace ℝ (Fin n)`). The rest of the file (finiteness, maximal-set extraction, norm/
separation translation) is PROVEN. Keep signature UNCHANGED; helpers `private`.

## KEY Mathlib bricks (verified present)
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`:
- `Measure.toSphere` (surface measure on `sphere 0 1`); `toSphere_apply_univ : μ.toSphere univ = (finrank ℝ E)*μ(ball 0 1)`.
- `toSphere_apply' (hs : MeasurableSet s) : μ.toSphere s = finrank ℝ E * μ (Ioo 0 1 • ((↑) '' s))` — cap measure = `n · vol(cone over cap)`.
- `measurePreserving_homeomorphUnitSphereProd` — polar disintegration `μ = toSphere ⊗ volumeIoiPow (n-1)`.
- `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball` — cap LOWER bound (WRONG direction; for reference).
`Mathlib/Topology/MetricSpace/CoveringNumbers.lean`: `maximalSeparatedSet`, `isCover_maximalSeparatedSet`,
`encard_maximalSeparatedSet`, `packingNumber`, the volume measure `volume` on `EuclideanSpace`.

## Strategy — cover bound needs the cap UPPER bound
Let `μ_S = (volume).toSphere`. A maximal `1/2`-separated `T` is a `1/2`-COVER (`isCover_maximalSeparatedSet`),
`|T| = packingNumber`. Cover ⇒ `𝕊 ⊆ ⋃_{t∈T} ball(t,1/2)`, so `μ_S(𝕊) ≤ Σ_t μ_S(cap(t,1/2))`. With a cap
UPPER bound `μ_S(cap(t,1/2)) ≤ 2^{-n} μ_S(𝕊)` ⇒ `μ_S(𝕊) ≤ |T|·2^{-n}μ_S(𝕊)` ⇒ `2^n ≤ |T|`.
**The cap upper bound** is the crux. Via `toSphere_apply'`: `μ_S(cap(t,1/2)) = n·vol(Ioo 0 1 • cap)`, and
`μ_S(𝕊) = n·vol(ball 0 1)`, so reduce to `vol(cone over cap(t,1/2)) ≤ 2^{-n}·vol(ball 0 1)`. The cone is
`{r•x : r∈(0,1), ‖x‖=1, ‖x-t‖<1/2} = {y : 0<‖y‖<1, ⟪y,t⟫ > (7/8)‖y‖}` (since `‖x-t‖²=2-2⟪x,t⟫<1/4`).

**WARNING — the constant is delicate.** The true cap fraction is `~(√15/8)^{n-1} < (1/2)^{n-1}`, so a clean
bound gives `~2^{n-1}` or `2^{n-2}`, NOT exactly `2^n` (the `sin^{n-2}` cap-angle integral that yields the
sharp `2^n` is not in Mathlib). Therefore:
- BEST: prove `vol(cone over cap(t,1/2)) ≤ 2^{-n} vol(ball)` by a crude containment if one exists (e.g. the
  cone ⊆ a half-ball or a scaled ball of radius `≤ 1/2`); if you can only get base `b<2`, you MAY weaken the
  statement's `2^n` to a provable `b^n` AND update `exists_sphere_packing` (`n·log 2 → n·log b`) — document the
  deviation per CLAUDE.md §1 (check `Examples/PCA.lean` still builds; it only needs exponential growth).
- ELSE: isolate the single sharp inequality `volume (Ioo 0 1 • (cap t (1/2))) ≤ 2^{-n} · volume (ball 0 1)`
  (or the `μ_S` form) as ONE named `private` lemma (one sorry + precise TODO) and prove the cover assembly
  around it — leaving a SMALLER, sharper residual than the current whole-packing one.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SpherePacking` green (0 sorry, or ≤1 sharper named residual).
`git add` SpherePacking.lean (+ `exists_sphere_packing`/`PCA.lean` ONLY if you changed the base constant); commit. Report.
