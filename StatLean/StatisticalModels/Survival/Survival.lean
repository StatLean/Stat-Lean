import StatLean.StatisticalModels.Survival.Defs
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.LeftRightLim

/-!
# The survival function — monotonicity, limits, CDF bridge

Basic analytic facts about `survival`/`survivalLeft` of an event-time law: monotonicity, range,
tail behavior, behavior on the negative half-line, the bridge to Mathlib's `ProbabilityTheory.cdf`
(whence right-continuity for free from the `StieltjesFunction` API), and the reconciliation of
the *defined* left limit `survivalLeft` with the topological left limit `Function.leftLim`.

**Reference.** ABGK §II.1 (verify §): the survival function and its regularity. CDF duality:
any probability text, e.g. TPE2 §1.2 (verify §).

**Proof formalization notes.** Everything here is measure monotonicity and continuity from
above/below (`measure_mono`, `tendsto_measure_iInter_atTop`-family) plus the `cdf` API
(`ProbabilityTheory.cdf` is a `StieltjesFunction`, so monotone + right-continuous are free).
`survivalLeft_eq_leftLim` is the one genuinely topological statement; it is a *bridge lemma* —
by design nothing downstream depends on it (the definition `S(t−) := μ [t, ∞)` is what the
Survival slice consumes).

**Bibliographic comments.** The identification of `P(T ≥ t)` with the left limit of
`P(T > ·)` is classical real analysis of monotone functions (Lebesgue); we record it only to
certify that the definitional choice agrees with the books' limit reading.
-/

open MeasureTheory Set Filter Topology

namespace StatLean.StatisticalModels.Survival

variable {μ : Measure ℝ}

/-- The survival function is antitone. -/
theorem antitone_survival (μ : Measure ℝ) : Antitone (survival μ) := by
  sorry

/-- The left-limit survival function is antitone. -/
theorem antitone_survivalLeft (μ : Measure ℝ) : Antitone (survivalLeft μ) := by
  sorry

/-- `S(t) ≤ S(t−)`. -/
theorem survival_le_survivalLeft (μ : Measure ℝ) (t : ℝ) :
    survival μ t ≤ survivalLeft μ t := by
  sorry

/-- The survival function of a probability law is bounded by one. -/
theorem survival_le_one [IsProbabilityMeasure μ] (t : ℝ) : survival μ t ≤ 1 := by
  sorry

/-- `S(t−) − S(t) = μ{t}`: the survival drop at `t` is the atom mass. -/
theorem survivalLeft_sub_survival (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    survivalLeft μ t = survival μ t + μ {t} := by
  sorry

/-- The survival function of a finite law vanishes at infinity. -/
theorem tendsto_survival_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (survival μ) atTop (𝓝 0) := by
  sorry

/-- An event-time law has full survival on the negative half-line. -/
theorem survival_of_neg
    -- USER-INPUT: event-time law (probability, supported on [0, ∞)); ABGK §II.1
    (h : IsEventTimeLaw μ) {t : ℝ} (ht : t < 0) :
    survival μ t = 1 := by
  sorry

/-- **CDF bridge**: `S(t) = 1 − F(t)` in real form; right-continuity of `survivalReal` then
comes free from the `StieltjesFunction` API of `ProbabilityTheory.cdf`. -/
theorem survivalReal_eq_one_sub_cdf [IsProbabilityMeasure μ] (t : ℝ) :
    survivalReal μ t = 1 - ProbabilityTheory.cdf μ t := by
  sorry

/-- Bridge lemma: the *defined* left limit `S(t−) = μ [t, ∞)` agrees with the topological
left limit of the survival function. Nothing downstream depends on this — it certifies the
definitional choice against the books' limit reading. -/
theorem survivalLeft_eq_leftLim (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    survivalLeft μ t = Function.leftLim (survival μ) t := by
  sorry

end StatLean.StatisticalModels.Survival
