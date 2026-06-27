import StatLean.Minimaxity.ForMathlib.TotalVariation
import StatLean.Minimaxity.ForMathlib.KLDivergence

/-!
# Pinsker–Csiszár–Kullback inequality — Lemma 15.2 (Wainwright §15.1.3)

The total variation distance is controlled by the Kullback–Leibler divergence:
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`  (Eq. (15.8)).

Wainwright outlines the proof in Exercise 15.6: reduce to the Bernoulli case via the partition
`A = {p ≥ q}` and Jensen's inequality. We state it with the `ℝ≥0∞` square root (`rpow (1/2)`), so the
bound is vacuously true when the KL divergence is infinite.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Pinsker–Csiszár–Kullback inequality** (Wainwright Lemma 15.2, Eq. (15.8)):
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2. -/
theorem pinsker_tv_le_kl (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  sorry

end StatLean.Minimaxity
