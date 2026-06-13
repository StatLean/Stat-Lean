Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`. Never `lake update`.
HARD ITEM — search Mathlib's measure/Haar API thoroughly; budget generously.

# CONTEXT (do NOT modify)
`Maximal/CoveringNumbers.lean` defines `IsEpsilonNet N s ε` and `coveringNumber s ε : ℕ∞`
(wrapping Mathlib `Metric.coveringNumber`). Read it for the exact shapes.

# TASK
Create `StatLean/ConcentrationInequalities/Maximal/CoveringBall.lean`
(namespace `StatLean.ConcentrationInequalities`) proving Lu *Big Data Analysis* §4.2
**Covering number of the ℓ²-ball** (`lm:covering-num`):

  theorem `coveringNumber_closedBall_le` : for `0 < ε < 1` and the closed unit ball
  `B = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1`,
  `coveringNumber B ε ≤ (1 + 2/ε) ^ d`  (as `ℕ∞`, or state the `≤ ((1+2/ε)^d : ℝ)` cardinality form).

# PROOF (volume / packing argument, Lu §4.2)
1. Take a MAXIMAL `ε`-separated subset `N ⊆ B` (pairwise distance `> ε`) via Zorn
   (`zorn_subset` / `Set.exists_maximal_…`). Maximality ⇒ `N` is an `ε`-net of `B`
   (else a point `> ε` from all of `N` could be added). So `coveringNumber B ε ≤ |N|`.
2. **Packing bound** (the named lemma `card_le_of_isSeparated_ball`): the open balls
   `ball(x, ε/2)` for `x ∈ N` are pairwise DISJOINT (separation `> ε`) and all contained in
   `ball(0, 1 + ε/2)`. By additivity + monotonicity of the volume (Haar) measure on `ℝ^d`,
   `|N| · vol(ball(0, ε/2)) ≤ vol(ball(0, 1+ε/2))`. Ball volumes scale as `r^d`
   (`MeasureTheory.Measure.addHaar_closedBall` / `addHaar_ball` / `Measure.addHaar_ball_mul`,
   in `EuclideanSpace`/`Fin d → ℝ` with `volume`), so
   `|N| ≤ ((1+ε/2)/(ε/2))^d = (1 + 2/ε)^d`.
   PROVE `card_le_of_isSeparated_ball` fully (ZERO sorry is the bar — it was previously an
   accepted-debt fallback). Key Mathlib bricks: `MeasureTheory.measure_biUnion_finset`
   (disjoint union measure = sum), `MeasureTheory.measure_mono`, `Measure.addHaar_ball`/
   `addHaar_closedBall` (ball volume `= r^d · vol(unit ball)`), and the scaling cancels the
   common `vol(unit ball)` factor. **Do NOT substitute a coordinate grid** — it corrupts the √d
   rate downstream in `thm:l2`.

If a TRULY irreducible Mathlib gap remains after a thorough, documented effort, isolate it as ONE
named `sorry` lemma `card_le_of_isSeparated_ball` with a precise docstring (goal + lemmas tried) and
prove everything else on top; report the sorry status prominently for escalation. Do NOT weaken the
`(1+2/ε)^d` constant.

§2 tags: `0 < ε`, `ε < 1` are USER-INPUT (Lu §4.2); measurability/finiteness regularity is LEAN-ONLY.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Maximal/CoveringBall.lean`.
# BUILD: srun -p shared -c 8 --mem=24G -t 1:00:00 lake build StatLean.ConcentrationInequalities.Maximal.CoveringBall
# DONE = build exits 0; ZERO sorries (or exactly one named card_le_of_isSeparated_ball if truly
# blocked); §2 tags; commit (`conc(maximal): covering number of ℓ²-ball ≤ (1+2/ε)^d (Lu-BDA §4.2 lm:covering-num)`).
# Report build status, exact sorry status, constant deviations. Independently re-verified.
