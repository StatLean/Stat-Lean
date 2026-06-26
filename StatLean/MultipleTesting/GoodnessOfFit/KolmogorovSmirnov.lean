import StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup

/-!
# Kolmogorov–Smirnov test — level guarantee (Candès, Lecture 3, §3.3.1)

The one-sided Kolmogorov–Smirnov test of the global null: reject when `KS⁺ = ksPlus p` exceeds the
threshold `u_α = √(log(n/α) / (2n))`. Its **level** (type-I error control) follows immediately from
the one-sided KS tail bound (`ForMathlib/EmpiricalProcessSup.ksPlus_tail_union`):

**Main result** (`ks_test_level`): under the global null (independent super-uniform p-values),
`μ{ KS⁺ ≥ u_α } ≤ α`, since the union tail `n·e^{−2n u_α²} = n·(α/n) = α`.

(With the sharp Massart constant the threshold improves to `√(log(2/α)/(2n))`; this version uses the
union-bound tail, which is the proved one.)

Reference: Candès, Lecture 3, §3.3.1, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Kolmogorov–Smirnov test level** (Candès, Lecture 3, §3.3.1, STAT 300C). Rejecting the global
null when `KS⁺ ≥ u_α` with `u_α = √(log(n/α)/(2n))` has type-I error at most `α`: directly from the
one-sided KS tail `ksPlus_tail_union`, since `n·e^{−2n u_α²} = α`. -/
theorem ks_test_level {n : ℕ} (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1
    (hnull : ∀ j, SuperUniform (p j) μ)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    μ {ω | Real.sqrt (Real.log ((n : ℝ) / α) / (2 * n)) ≤ ksPlus p ω} ≤ ENNReal.ofReal α := by
  sorry

end StatLean.MultipleTesting
