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
  set u := Real.sqrt (Real.log ((n : ℝ) / α) / (2 * n)) with hu_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  -- `n/α ≥ 1` (since `α < 1 ≤ n`), hence `log(n/α) ≥ 0`, hence the sqrt argument is `≥ 0`.
  have hαn : α ≤ (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) / α) := Real.log_nonneg ((one_le_div hα0).2 hαn)
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have harg_nonneg : 0 ≤ Real.log ((n : ℝ) / α) / (2 * n) := div_nonneg hlog_nonneg h2n.le
  have husq : u ^ 2 = Real.log ((n : ℝ) / α) / (2 * n) := Real.sq_sqrt harg_nonneg
  -- Plug the threshold `u = u_α` (which is `≥ 0`) into the one-sided union-bound KS tail.
  refine le_trans (ksPlus_tail_union μ p hmeas hindep hnull hn (Real.sqrt_nonneg _)) (le_of_eq ?_)
  -- It remains to simplify `n · e^{−2n u²} = α`.
  congr 1
  rw [husq]
  have hexp_arg : -2 * (n : ℝ) * (Real.log ((n : ℝ) / α) / (2 * n)) = -Real.log ((n : ℝ) / α) := by
    field_simp
  rw [hexp_arg, Real.exp_neg, Real.exp_log (div_pos hnR hα0), inv_div, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hnR']

end StatLean.MultipleTesting
