# Close the Chapter-5 packing existence debts (Hamming/Sphere/Sparse)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun.
FOREGROUND builds only. These are HARD combinatorics; close what you honestly can.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/Packing/HammingPacking.lean`  (`gilbert_varshamov`)
- `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean`   (`sphere_packing_card`)
- `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean`   (`sparse_packing`)
Keep public signatures/docstrings UNCHANGED. Helpers `private`.

## Strategy
- `gilbert_varshamov` (Ex 5.3): a `m/4`-separated `T ⊆ {0,1}^m`, `log|T| ≥ m/10`. Take a MAXIMAL
  `m/4`-separated set (exists by finiteness — `Finset` + `Set.Finite`/Zorn on a finite type). By maximality
  its radius-`m/4` Hamming balls cover `{0,1}^m`, so `|T| · maxBallCard ≥ 2^m`. Bound the Hamming-ball
  volume `Σ_{i≤m/4} C(m,i) ≤ 2^{m·H₂(1/4)}` with `H₂(1/4) = (1/4)log₂4 + (3/4)log₂(4/3) ≤ 0.82 < 9/10`
  (so `log|T| ≥ m·log2·(1−0.82) ≥ m/10`). Mathlib: `Nat.choose`, `hammingDist`, `Finset.card`,
  `Real.binEntropy`, sum-of-binomials bound. This is the hardest; if the entropy volume bound resists,
  isolate it as ONE named `private` lemma `hamming_ball_card_le` (sorry) and prove the rest around it.
- `sphere_packing_card` (Ex 5.8): `≥ 2^n` unit vectors of `ℝⁿ` pairwise `≥1/2`-separated. Maximal
  `1/2`-separated subset of the unit sphere; disjoint radius-`1/4` balls ⊂ radius-`5/4` ball ⇒ count
  `≥ (5/4 / (1/4))^? ` … use the standard volume ratio. Mathlib: `EuclideanSpace`, `Metric.ball`,
  `MeasureTheory.volume`, `Measure.addHaar_ball` / `volume` of balls in `ℝⁿ`. Isolate the volume crux.
- `sparse_packing` (Ex 5.8): over `C(d,s)` supports run the sphere packing per support; combine.

GOAL: maximize closure; for each theorem either fully close, or reduce to ONE smaller named `private`
crux lemma (single sorry + precise `-- TODO(mmx)`).

## DONE
`lake build` each module green; commit `git add` ONLY the three files. Report per-theorem closed vs
reduced-to-named-crux + the Mathlib lemmas used.
