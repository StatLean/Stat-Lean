import StatLean.Bayesian.Cond.Defs

/-!
# Law of total probability and finite-partition Bayes' theorem

For a finite measurable partition `{H i}ᵢ∈ₛ` of the sample space and observed data `d`, this file
proves the **law of total probability**
$$\mu(d) = \sum_{i \in s} \mu[d \mid H_i]\,\mu(H_i),$$
the **finite-partition Bayes' theorem**
$$\mu[H_j \mid d] = \frac{\mu[d \mid H_j]\,\mu(H_j)}{\sum_{i \in s} \mu[d \mid H_i]\,\mu(H_i)},$$
and the **two-hypothesis Bayes' theorem** (the `{t, tᶜ}` special case).

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §1.2, p. 8 (two-event
Bayes' theorem and its total-probability denominator); Example 1.2.3 (Laplace), p. 11 (finite
discrete Bayes). Robert states these via prose and numbered equations rather than as a standalone
numbered theorem.

**Proof formalization notes.** Built directly on Mathlib's `ProbabilityTheory.cond`
(`μ[d | H i] = cond μ (H i) d`). We work in `ℝ≥0∞` with `[IsFiniteMeasure μ]`, which removes all
`∞` cases; degenerate parts (`μ (H i) = 0`) contribute `0` to both sides under the
extended-nonnegative conventions (`0/0 = 0`), so **no positivity hypotheses are needed**. Key
Mathlib bricks: `cond_mul_eq_inter`, `cond_add_cond_compl_eq`, `cond_apply'`,
`measure_biUnion_finset`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- **Law of total probability** over a finite measurable partition:
`μ d = ∑ i ∈ s, μ[d | H i] * μ (H i)`. Parts with `μ (H i) = 0` contribute `0` to both sides,
so no positivity hypotheses are needed (Robert §1.2, the total-probability denominator, p. 8). -/
theorem measure_eq_sum_cond_mul_of_partition {s : Finset ι} {H : ι → Set Ω}
    -- LEAN-ONLY: the hypotheses `H i` are events (measurability is measure-theoretic regularity)
    (hHm : ∀ i ∈ s, MeasurableSet (H i))
    -- USER-INPUT: the hypotheses are mutually exclusive; Robert §1.2
    (hHd : (s : Set ι).PairwiseDisjoint H)
    -- USER-INPUT: the hypotheses are exhaustive; Robert §1.2
    (hHc : ⋃ i ∈ s, H i = Set.univ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the observed data `d` is an event (measurability is regularity)
    {d : Set Ω} (hd : MeasurableSet d) :
    μ d = ∑ i ∈ s, μ[d | H i] * μ (H i) := sorry

/-- **Bayes' theorem for a finite partition** (Robert §1.2, discrete posterior form). If
`μ d = 0` both sides are `0` (`0/0 = 0` in `ℝ≥0∞`), so the observed-data event needs no
positivity hypothesis. -/
theorem cond_eq_cond_mul_div_sum_of_partition {s : Finset ι} {H : ι → Set Ω}
    -- LEAN-ONLY: the hypotheses `H i` are events
    (hHm : ∀ i ∈ s, MeasurableSet (H i))
    -- USER-INPUT: the hypotheses are mutually exclusive; Robert §1.2
    (hHd : (s : Set ι).PairwiseDisjoint H)
    -- USER-INPUT: the hypotheses are exhaustive; Robert §1.2
    (hHc : ⋃ i ∈ s, H i = Set.univ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the observed data `d` is an event
    {d : Set Ω} (hd : MeasurableSet d) {j : ι} (hj : j ∈ s) :
    μ[H j | d] = μ[d | H j] * μ (H j) / ∑ i ∈ s, μ[d | H i] * μ (H i) := sorry

/-- **Two-hypothesis Bayes' theorem** (Robert §1.2, p. 8). Only the hypothesis `t` needs
measurability; the data `d` may be any set (`cond_apply'` / `cond_add_cond_compl_eq` take the
target set arbitrary). Degenerate cases vanish under the `ℝ≥0∞` conventions. -/
theorem cond_eq_cond_mul_div_add_compl (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the hypothesis `t` is an event
    {t : Set Ω} (ht : MeasurableSet t) (d : Set Ω) :
    μ[t | d] = μ[d | t] * μ t / (μ[d | t] * μ t + μ[d | tᶜ] * μ tᶜ) := sorry

end StatLean.Bayesian
