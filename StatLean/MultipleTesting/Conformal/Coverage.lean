import StatLean.MultipleTesting.ForMathlib.RankUniform

/-!
# Conformal prediction coverage — assembly (Candès, Lecture 9, §9.6, Theorem 2)

Split-conformal prediction. Given calibration nonconformity scores `S₀, …, S_{n-1}` and a test
score `S_n` (so `m = n+1` scores `S : Fin (n+1) → Ω → ℝ`), all **exchangeable** and a.s. distinct,
the prediction set `Ĉ` formed from the `⌈(n+1)(1−α)⌉`-th smallest calibration score covers the test
point with probability at least `1 − α`.

**Main result** (`conformal_coverage`): with `k = ⌈(n+1)(1−α)⌉`,
`1 − α ≤ μ{ rankOf S (last) ≤ k }`. The covering event `Y_{n+1} ∈ Ĉ` is exactly
`{ S_n ≤ (k-th smallest score) } = { rankOf S (last) ≤ k }` (the test score is among the `k`
smallest); so this is the `1 − α` coverage guarantee.

*Proof.* By rank uniformity (`measure_rankOf_le`), `μ{ rankOf S (last) ≤ k } = k/(n+1)`, and
`k = ⌈(n+1)(1−α)⌉ ≥ (n+1)(1−α)` gives `k/(n+1) ≥ 1−α`.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Conformal coverage** (Candès, Lecture 9, §9.6, Theorem 2, STAT 300C). For `n+1` exchangeable,
a.s. distinct scores, the split-conformal prediction set built from the `⌈(n+1)(1−α)⌉`-th smallest
score covers the test point (the `rankOf S (last) ≤ k` event) with probability at least `1 − α`. -/
theorem conformal_coverage {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (S : Fin (n + 1) → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- USER-INPUT: each score is measurable; Candès L9 §9.6
    (hmeas : ∀ i, Measurable (S i))
    -- USER-INPUT: the scores are exchangeable (calibration + test i.i.d./exchangeable); Candès L9 §9.6
    (hExch : Exchangeable S μ)
    -- USER-INPUT: the scores are a.s. pairwise distinct; Candès L9 §9.6
    (hdistinct : ∀ᵐ ω ∂μ, Function.Injective (fun i => S i ω)) :
    (ENNReal.ofReal (1 - α)) ≤
      μ {ω | rankOf S (Fin.last n) ω ≤ ⌈((n : ℝ) + 1) * (1 - α)⌉₊} := by
  sorry

end StatLean.MultipleTesting
