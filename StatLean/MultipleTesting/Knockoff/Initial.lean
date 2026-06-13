import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.ForMathlib.BinomialRatio

/-!
# Knock-off initial bound (Lu-BDA §19)

`knockoff_initial_le`: `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` every (non-tied) null is counted,
`V₊(0) + V₋(0) = N₀`, and by the knock-off sign field (Def. `kos` cond. 3, i.e.
`KnockoffScore.signs_iIndep`/`signs_fair`) `V₊(0) ~ Binomial(N₀, ½)`. The integral becomes the
finite sum bounded by `binom_ratio_sum_le_one`.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Initial bound (Lu-BDA §19): `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` the null positives
`V₊(0)` are `Binomial(N₀, ½)`-distributed (the null signs are i.i.d. fair coins), and the
expectation reduces to `binom_ratio_sum_le_one`. -/
theorem knockoff_initial_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) :
    ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ ≤ 1 := by
  sorry

end StatLean.MultipleTesting
