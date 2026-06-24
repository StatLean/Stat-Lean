import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
import StatLean.ConcentrationInequalities.SubExponential.Defs
import StatLean.HighDimensionalStatistics.LinearModel.Defs
import Mathlib.Probability.Independence.Basic

/-!
# χ²₁ sub-exponentiality and the fixed-`β` quadratic-form tail

The probabilistic core of the random-RIP theorem (Lu, *Big Data Analysis* §7,
`thm:3s-rip`, eq:fix-b). Two results:

* `chiSq1_centered_isSubExponential` — for `g ∼ N(0,1)`, the centered square `g² − 1`
  is sub-exponential with parameter `α = 4`. Proof via the closed-form χ²₁ MGF
  `E[exp(t(g²−1))] = e^{−t}(1−2t)^{-1/2} ≤ exp(8t²)` for `|t| ≤ 1/4`, computed from the
  Gaussian integral `∫ exp(−bx²) dN(0,1) = (1−2b)^{-1/2}` (`integral_gaussian`).

* `gaussian_quadratic_form_tail` — for an i.i.d. `N(0,1/n)` matrix `X` and a fixed
  nonzero `β`, the normalised quadratic form concentrates:
  `P(|‖Xβ‖²/‖β‖² − 1| > δ) ≤ 2·exp(−nδ²/8)`. Proof: `‖Xβ‖²/‖β‖² = (1/n)∑ᵢ gᵢ²` with
  `gᵢ ∼ N(0,1)` i.i.d. (rows are Gaussian via `GaussianMGF`); apply
  `chiSq1_centered_isSubExponential` and the sub-exponential sample-mean tail, two-sided.

Concept-layer for the compressed-sensing sub-area; consumed by `RandomRIP.lean`.
Constants (`8`, `α=4`) are the provable ones; document any deviation from the book.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Centered χ²₁ is sub-exponential** (Lu §7, used for eq:fix-b). For `g ∼ N(0,1)`,
`g² − 1` is sub-exponential with parameter `α = 4`. -/
theorem chiSq1_centered_isSubExponential
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ)
    -- USER-INPUT: g is measurable; Lu-BDA §7 (thm:3s-rip)
    (hg_meas : Measurable g)
    -- USER-INPUT: g ∼ N(0,1); Lu-BDA §7 (thm:3s-rip)
    (hg : Measure.map g μ = gaussianReal 0 1) :
    IsSubExponential (fun ω => g ω ^ 2 - 1) 4 μ := by
  sorry

/-- **Fixed-`β` quadratic-form tail** (Lu §7, eq:fix-b). If `X` has i.i.d. `N(0,1/n)`
entries then for any fixed `β ≠ 0`,
`P(|‖Xβ‖²/‖β‖² − 1| > δ) ≤ 2·exp(−n δ²/8)`. -/
theorem gaussian_quadratic_form_tail
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    -- USER-INPUT: the entries Xᵢⱼ are jointly independent; Lu-BDA §7 (thm:3s-rip)
    (hindep : iIndepFun (fun (p : Fin n × Fin d) ω => X ω p.1 p.2) μ)
    -- USER-INPUT: each entry Xᵢⱼ ∼ N(0,1/n); Lu-BDA §7 (thm:3s-rip)
    (hlaw : ∀ i j, Measure.map (fun ω => X ω i j) μ
              = gaussianReal 0 (⟨1 / (n : ℝ), div_nonneg zero_le_one (Nat.cast_nonneg n)⟩ : ℝ≥0))
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | δ < |‖designMap (X ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 8)) := by
  sorry

end StatLean.HighDimensionalStatistics
