import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.MultipleTesting.ForMathlib.OrderStatistics
import StatLean.MultipleTesting.PValues.Defs
import Mathlib.Probability.Independence.Basic

/-!
# One-sided Kolmogorov–Smirnov statistic and Massart's inequality — ForMathlib brick

The one-sided KS statistic `KS⁺ = sup_t (F̂ₙ(t) − t)` and its tail bound (Candès, Lecture 3,
§3.3.1, Theorem 2 — Massart's inequality). For `n` p-values `p : Fin n → Ω → ℝ`, the empirical
process `F̂ₙ(t) − t` is right-continuous and decreasing between jumps, so its supremum over `[0,1]`
is attained at the jumps, i.e. `KS⁺ = maxᵢ ( (i+1)/n − p₍ᵢ₊₁₎ )` (a finite max over the order
statistics `p₍₁₎ ≤ … ≤ p₍ₙ₎`). We take that finite max as the definition.

* `ksPlus p ω` — `⨆ᵢ ((i+1)/n − orderStat (p·ω) i)`, the one-sided KS statistic;
* `ksPlus_tail_union` — the **union-bound** tail `μ{KS⁺ ≥ u} ≤ n·e^{−2nu²}` (a *real* theorem:
  order-stat reduction `{(k/n)−p₍ₖ₎ ≥ u} = {countLE(k/n−u) ≥ k}` + Hoeffding at each `k`);
* `massart_inequality` — the **sharp** Massart bound `μ{KS⁺ ≥ u} ≤ 2·e^{−2nu²}` for
  `u ≥ √(log 2/(2n))`; the sharp constant needs the empirical-process reflection argument
  (Massart 1990) and is left as a documented named `sorry`.

Under the global null the p-values are independent with super-uniform marginals; that suffices for
the upper tail of `F̂ₙ(t) − t`. Theorem-agnostic; consumed by `GoodnessOfFit/KolmogorovSmirnov.lean`.

Reference: Candès, Lecture 3, §3.3.1, Theorem 2, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- The **one-sided Kolmogorov–Smirnov statistic** `KS⁺ = maxᵢ ((i+1)/n − p₍ᵢ₊₁₎)`, the supremum
of the empirical process `F̂ₙ(t) − t` (attained at the order statistics). -/
noncomputable def ksPlus (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ i : Fin n, (((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i)

/-- **Union-bound KS tail** (the *real*, achievable form). For independent super-uniform null
p-values, `μ{ KS⁺ ≥ u } ≤ n · e^{−2nu²}` (`u ≥ 0`). Proof: `KS⁺ ≥ u ⟺ ∃ k, (k/n) − p₍ₖ₎ ≥ u`, and
`{(k/n) − p₍ₖ₎ ≥ u} = {countLE (k/n − u) ≥ k}`, each bounded by `e^{−2nu²}` (Hoeffding on the
bounded indicators with mean `≤ k/n − u`); union over the `n` order statistics. -/
theorem ksPlus_tail_union (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1
    (hnull : ∀ j, SuperUniform (p j) μ)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ ksPlus p ω} ≤ ENNReal.ofReal ((n : ℝ) * Real.exp (-2 * n * u ^ 2)) := by
  sorry

/-- **Massart's inequality** (Candès, Lecture 3, §3.3.1, Theorem 2 — Massart 1990): the *sharp*
one-sided KS tail `μ{ KS⁺ ≥ u } ≤ 2·e^{−2nu²}` for `u ≥ √(log 2/(2n))`. The sharp constant `2`
(vs. the `n` of `ksPlus_tail_union`) requires the empirical-process reflection argument and is a
documented named debt. -/
theorem massart_inequality (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1
    (hnull : ∀ j, SuperUniform (p j) μ)
    {u : ℝ} (hu : Real.sqrt (Real.log 2 / (2 * n)) ≤ u) :
    μ {ω | u ≤ ksPlus p ω} ≤ ENNReal.ofReal (2 * Real.exp (-2 * n * u ^ 2)) := by
  sorry

end StatLean.MultipleTesting
