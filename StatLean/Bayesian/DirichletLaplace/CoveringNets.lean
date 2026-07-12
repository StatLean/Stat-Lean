import StatLean.ConcentrationInequalities.Maximal.CoveringBall
import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite ε-nets of Euclidean balls, as `Finset`s (C10)

The shell decomposition of the DL contraction proof (`ShellDecomposition`) needs, for each support
set `S`, an explicit **finite** ε-net of a Euclidean ball together with a cardinality bound. Mathlib
and the concentration-inequalities area already provide the volumetric covering-number estimate
`coveringNumber (closedBall 0 1) ε ≤ ⌊(1 + 2/ε)^d⌋` (`CoveringBall.lean`, Lu-BDA §6.2). This file
repackages it into the ready-to-use existential form — a `Finset F` of centres, each in the ball,
covering the ball to accuracy `ε`, with `|F| ≤ (1 + 2/ε)^d` — and lifts it from the unit ball to an
arbitrary ball `B(x₀, R)` in any finite-dimensional real inner-product space (cardinality bound
`(1 + 2R/ε)^{finrank}`).

Both statements reuse the covering bricks; no new geometry is proved here. The unit-ball extraction
mirrors `HighDimensionalStatistics/CompressedSensing/RandomRIP.lean`'s `exists_quarter_net`
(minimal-cover / `encard` idiom). This cross-area import of the concentration-inequalities concept
layer follows that established precedent.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 6 (Bernstein and Maximal Inequalities), §6.2 — Definition 6.2
(ε-Net) and Lemma 6.1 (Covering Number). Used in BPPD §6 as the sieve/net over each support shell.

**Proof formalization notes.** `exists_finset_net_unitBall`: instantiate
`coveringNumber_closedBall_le` at radius `ε`, then extract a `Finset` from the finite
`Metric.minimalCover` exactly as `exists_quarter_net` does (`Metric.finite_minimalCover`,
`Metric.encard_minimalCover`, `Metric.isCover_minimalCover`, `Set.Finite.toFinset`).
`exists_finset_net_closedBall`: transport an orthonormal-basis isometry `E ≃ₗᵢ EuclideanSpace ℝ (Fin
(finrank))` (`stdOrthonormalBasis`) to reduce to `EuclideanSpace ℝ (Fin d)`, then scale by `R` and
translate by `x₀` (a net of `B(0,1)` at accuracy `ε/R` dilates to a net of `B(x₀, R)` at accuracy
`ε`, with the cardinality bound `(1 + 2/(ε/R))^d = (1 + 2R/ε)^{finrank}`).
-/

open MeasureTheory Metric
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

open StatLean.ConcentrationInequalities

variable {ι : Type*} [Fintype ι]

/-- **Explicit finite ε-net of the Euclidean unit ball** (Lu-BDA §6.2, `Finset` packaging).

For `0 < ε < 1` and `d ≥ 1` there is a finite set `F ⊆ B(0, 1) ⊆ ℝ^d` of centres, covering the
closed unit ball to accuracy `ε` (every point is within `ε` of some centre), with
`|F| ≤ (1 + 2/ε)^d`. This is the existential/`Finset` form of `coveringNumber_closedBall_le`. -/
lemma exists_finset_net_unitBall (d : ℕ) [NeZero d] {ε : ℝ}
    -- USER-INPUT: 0 < ε (net accuracy positive); Lu-BDA §6.2, Lemma 6.1
    (hε : 0 < ε)
    -- USER-INPUT: ε < 1 (matches the book's covering-number regime); Lu-BDA §6.2, Lemma 6.1
    (hε1 : ε < 1) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin d)),
      ↑F ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ∃ c ∈ F, dist x c ≤ ε) ∧
      (F.card : ℝ) ≤ (1 + 2 / ε) ^ d := by
  sorry

/-- **Explicit finite ε-net of an arbitrary Euclidean ball** (Lu-BDA §6.2, general form).

In any finite-dimensional real inner-product space `E`, the closed ball `B(x₀, R)` (with `0 < ε < R`)
has a finite ε-net `F ⊆ B(x₀, R)` with `|F| ≤ (1 + 2R/ε)^{finrank ℝ E}`. Obtained from the unit-ball
net by an orthonormal-basis isometry to `EuclideanSpace ℝ (Fin (finrank))`, scaling by `R`, and
translating by `x₀`. -/
lemma exists_finset_net_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x₀ : E) (R ε : ℝ)
    -- USER-INPUT: 0 < R (ball radius positive); Lu-BDA §6.2, Lemma 6.1
    (hR : 0 < R)
    -- USER-INPUT: 0 < ε (net accuracy positive); Lu-BDA §6.2, Lemma 6.1
    (hε : 0 < ε)
    -- USER-INPUT: ε < R (net finer than the ball); Lu-BDA §6.2, Lemma 6.1
    (hεR : ε < R) :
    ∃ F : Finset E,
      ↑F ⊆ Metric.closedBall x₀ R ∧
      (∀ x ∈ Metric.closedBall x₀ R, ∃ c ∈ F, dist x c ≤ ε) ∧
      (F.card : ℝ) ≤ (1 + 2 * R / ε) ^ (Module.finrank ℝ E) := by
  sorry

end StatLean.Bayesian
