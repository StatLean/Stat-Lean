import StatLean.Bayesian.Cond.FinitePartition

/-!
# Posterior odds and the Bayes factor

The odds reformulation of Bayes' theorem for a single hypothesis event `s` against `sᶜ`:

* **posterior odds = prior odds × Bayes factor**
  $$\frac{\mu[s \mid d]}{\mu[s^c \mid d]} = \frac{\mu(s)}{\mu(s^c)} \cdot \frac{\mu[d \mid s]}{\mu[d \mid s^c]};$$
* the **Bayes factor as the odds ratio** `bayesFactor = posteriorOdds / priorOdds`.

**Reference.** C. P. Robert, *The Bayesian Choice*, 2nd ed., Springer, 2007. §1.2 (odds form of
Bayes' theorem, eq. (1.2.2), p. 9); §5.2.2, Definition 5.2.5 (Bayes factor) and eq. (5.2.2),
p. 227.

**Proof formalization notes.** Everything unfolds to Mathlib's `ProbabilityTheory.cond` and
`ℝ≥0∞` division. The factorization identity is stated *unconditionally*: under `[IsFiniteMeasure μ]`
the generic case reduces to `ENNReal.mul_div_mul_left` with the nonzero, non-infinite factor
`(μ d)⁻¹`, and every degenerate case (`μ d`, `μ s`, or `μ sᶜ` equal to `0`) makes both sides `0`
or both `∞`. The *inversion* (`bayesFactor = posteriorOdds / priorOdds`) does need nondegenerate
priors `μ s ≠ 0`, `μ sᶜ ≠ 0` (else the odds ratio is `0/0` junk), which is exactly Robert's
standing assumption in Definition 5.2.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Posterior odds = prior odds × Bayes factor** (Robert §1.2, eq. (1.2.2); Definition 5.2.5).
Holds unconditionally for a finite measure: all degenerate cases collapse both sides under the
`ℝ≥0∞` conventions. -/
theorem posteriorOdds_eq_priorOdds_mul_bayesFactor (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the hypothesis `s` is an event
    {s : Set Ω} (hs : MeasurableSet s) (d : Set Ω) :
    posteriorOdds μ s d = priorOdds μ s * bayesFactor μ s d := sorry

/-- **Bayes factor as the odds ratio** (Robert Definition 5.2.5). Nondegeneracy of the prior is a
genuine input: without positive prior mass on both `s` and `sᶜ` the ratio is `0/0` junk. -/
theorem bayesFactor_eq_posteriorOdds_div_priorOdds (μ : Measure Ω) [IsFiniteMeasure μ]
    -- LEAN-ONLY: the hypothesis `s` is an event
    {s : Set Ω} (hs : MeasurableSet s) (d : Set Ω)
    -- USER-INPUT: the hypothesis has positive prior probability; Robert Definition 5.2.5
    (hs0 : μ s ≠ 0)
    -- USER-INPUT: the alternative has positive prior probability; Robert Definition 5.2.5
    (hsc0 : μ sᶜ ≠ 0) :
    bayesFactor μ s d = posteriorOdds μ s d / priorOdds μ s := sorry

end StatLean.Bayesian
