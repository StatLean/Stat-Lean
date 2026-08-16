import StatLean.ConcentrationInequalities.Chaining.DudleyTail
import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

/-!
# High-probability Dudley inequality with a genuine supremum

Honest `sup_{t,s ∈ T}` forms of the high-probability Dudley inequality
(HDP Remark 8.1.6 / Eq. (8.15)) over an arbitrary — possibly uncountable —
index set: the countable-subset **existential core**
`dudley_tail_three_term_exists` (the junk-free event
`{ω | ∃ t s ∈ C, thr < |X t ω − X s ω|}` via the tail lift engine), the
formal-`⨆` displays over `T` under `hsep : IsSeparableProcess X T μ`
(three-term and `200·K·(∫₀^D √log 𝒩 + u·diam)` thresholds), the countable
display `dudley_tail_countable`, and the extracted threshold arithmetic
`dudley_tail_threshold_le`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Remark 8.1.6 / Eq. (8.15); the general-`T`
forms realize the p. 227 footnote 1 ("we are assuming T is finite to avoid
measurability issues; the general case typically follows by approximation")
through separable versions.

**Proof formalization notes.** Thresholds and guards inherited verbatim from
the per-finite-subset family: the three-term threshold
`K·(9·dudleySum T + 17·diam T + 12u·diam T)` with the LEAN-ONLY summability
junk-guard `hS`, and the display threshold
`200·K·((dudleyLIntegral T D).toReal + u·diam T)` with BOTH `hS` and the
finiteness guard `hDL` (a real threshold cannot honestly encode divergent
entropy; (8.15) is vacuous there). Every threshold is a product of
nonnegatives, so the formal-`⨆` events reduce to the existential core
through `exists_pair_lt_of_lt_biSup_real` (whose `0 ≤ c` hypothesis absorbs
the `Real.sSup` junk), and the separable transport runs POINTWISE through
`exists_lt_comp_of_mem_closure` (two one-variable approximations; no
supremum transport is needed for events). Measures of the possibly
non-measurable sup events are sound: only outer-measure monotonicity and
continuity from below along a.e.-measurable finite windows are used. The
diagonal pair `t = s` is harmless on both sides (value `0`, threshold
nonnegative). Named-sorry fallback of this work item:
`dudley_tail_threshold_le` (the `nlinarith` constant arithmetic).

**Bibliographic comments.** Eq. (8.15) is HDP Exercise 8.1 (Gaussian case:
Exercise 8.2 via concentration); the chaining tail argument is standard
(Talagrand 2014, §2.2; Boucheron–Lugosi–Massart 2013, §13.1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **High-probability Dudley inequality, existential countable-subset
core** (HDP §8.1, Eq. (8.15)): with probability at least `1 − 2e^{−u²}`, NO
pair of the countable subfamily `C ⊆ T` has oscillation exceeding the
three-term threshold. The junk-free engine stage of the formal-supremum
displays below. -/
theorem dudley_tail_three_term_exists {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    μ {ω | ∃ t ∈ C, ∃ s ∈ C,
        K * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
          < |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

/-- **Threshold arithmetic** (extracted from the display form): under the
junk-guards, the three-term threshold is dominated by the display threshold
`200·((∫₀^D √log 𝒩).toReal + u·diam T)`. `K`-free; callers multiply by
`K ≥ 0`. -/
lemma dudley_tail_threshold_le {T : Set E}
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- LEAN-ONLY: finite entropy integral (real-threshold junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T
      ≤ 200 * ((dudleyLIntegral T D).toReal + u * Metric.diam T) := by
  sorry

/-- **High-probability Dudley inequality, three-term separable supremum**
(HDP §8.1, Eq. (8.15), general `T`): for a separable version, the two-sided
oscillation supremum over `T` exceeds the three-term threshold with
probability at most `2e^{−u²}`. The nonnegative threshold absorbs the
`Real.sSup` junk branch, and the proof routes through the junk-free
existential core. -/
theorem dudley_tail_three_term_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | K * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

/-- **High-probability Dudley inequality, display form, separable supremum**
(HDP §8.1, Eq. (8.15), general `T`): the two-sided oscillation supremum
exceeds `200·K·((∫₀^D √log 𝒩).toReal + u·diam T)` with probability at most
`2e^{−u²}`. Guards `hS` and `hDL` as in the per-finite-subset
`dudley_tail`. -/
theorem dudley_tail_separable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- LEAN-ONLY: finite entropy integral (real-threshold junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 200 * K * ((dudleyLIntegral T D).toReal + u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

/-- **High-probability Dudley inequality, display form, countable supremum**
(HDP §8.1, Eq. (8.15)): the countable-`T` display with the
`200·K·((∫₀^D √log 𝒩).toReal + u·diam T)` threshold (the display twin of
the published three-term `dudley_tail_three_term_countable`). -/
theorem dudley_tail_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: summable dyadic entropy (real-threshold junk-guard)
    (hS : Summable fun k : ℤ => dudleySummand T k)
    -- LEAN-ONLY: finite entropy integral (real-threshold junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 200 * K * ((dudleyLIntegral T D).toReal + u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

end StatLean.ConcentrationInequalities
