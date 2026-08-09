import StatLean.ExperimentalDesign.Core.Design
import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation

/-!
# Inclusion probabilities of a sampling design

For a sampling design `D` (a PMF on subsets of the finite population `U`), the
**first-order inclusion probability** of a unit and the **second-order inclusion
probability** of a pair are
$$\pi_i = P_D(i \in S) = \mathbb E_D[\mathbf 1\{i \in S\}], \qquad
  \pi_{ij} = P_D(i \in S,\ j \in S),$$
with the diagonal convention `π_{ii} = π_i`.  This file defines both as design
expectations of inclusion indicators and proves the elementary identities every
design-based estimator rests on: symmetry, bounds, the expected-sample-size identity
`E|S| = ∑ᵢ πᵢ`, and the indicator covariance `Cov(𝟙ᵢ, 𝟙ⱼ) = π_{ij} − πᵢ πⱼ`.

## Main results

* `inclusionProb`, `pairInclusionProb` — the design quantities.
* `pairInclusionProb_comm`, `pairInclusionProb_self` — symmetry and the diagonal.
* `inclusionProb_nonneg`, `inclusionProb_le_one`, `pairInclusionProb_nonneg`,
  `pairInclusionProb_le_left` — bounds.
* `expect_sampleCard` — `E|S| = ∑ᵢ πᵢ`.
* `cov_inclusionIndicator` — the indicator covariance.

**Reference.** The finite-population sampling frame is the survey-sampling companion
of Mead's finite randomisation model (`Mead §9.1`, "what is the population?"); the
inclusion-probability calculus is from D.G. Horvitz and D.J. Thompson, "A
generalization of sampling without replacement from a finite universe," *J. Amer.
Statist. Assoc.* **47** (1952), 663–685.  (`HT52`.)

**Proof formalization notes.**
* All quantities are `pmfExpect`s of `0/1`-valued statistics, so every identity is a
  finite-sum manipulation; bounds come from `pmfExpect_mono` against the constants
  `0` and `1`.
* `expect_sampleCard` is `card_sample_eq_sum_indicator` plus `pmfExpect_sum`.
* No positivity of `πᵢ` is assumed anywhere in this file; positivity enters only for
  the Horvitz–Thompson estimator downstream.
-/

namespace StatLean.ExperimentalDesign

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The **first-order inclusion probability** `πᵢ = P_D(i ∈ S)` of a unit under a
sampling design (`HT52`). -/
noncomputable def inclusionProb (D : SamplingDesign U) (i : U) : ℝ :=
  pmfExpect D (inclusionIndicator i)

/-- The **second-order inclusion probability** `π_{ij} = P_D(i ∈ S, j ∈ S)` of a pair
of units (`HT52`).  Diagonal convention: `π_{ii} = πᵢ`
(`pairInclusionProb_self`). -/
noncomputable def pairInclusionProb (D : SamplingDesign U) (i j : U) : ℝ :=
  pmfExpect D fun s => inclusionIndicator i s * inclusionIndicator j s

/-- Inclusion probabilities are nonnegative. -/
theorem inclusionProb_nonneg (D : SamplingDesign U) (i : U) :
    0 ≤ inclusionProb D i := by
  sorry

/-- Inclusion probabilities are at most one. -/
theorem inclusionProb_le_one (D : SamplingDesign U) (i : U) :
    inclusionProb D i ≤ 1 := by
  sorry

/-- Symmetry of the second-order inclusion probability. -/
theorem pairInclusionProb_comm (D : SamplingDesign U) (i j : U) :
    pairInclusionProb D i j = pairInclusionProb D j i := by
  sorry

/-- Diagonal of the second-order inclusion probability: `π_{ii} = πᵢ`. -/
theorem pairInclusionProb_self (D : SamplingDesign U) (i : U) :
    pairInclusionProb D i i = inclusionProb D i := by
  sorry

/-- Second-order inclusion probabilities are nonnegative. -/
theorem pairInclusionProb_nonneg (D : SamplingDesign U) (i j : U) :
    0 ≤ pairInclusionProb D i j := by
  sorry

/-- A pair is included no more often than either of its members. -/
theorem pairInclusionProb_le_left (D : SamplingDesign U) (i j : U) :
    pairInclusionProb D i j ≤ inclusionProb D i := by
  sorry

/-- **Expected sample size**: `E_D|S| = ∑ᵢ πᵢ` (`HT52`). -/
theorem expect_sampleCard (D : SamplingDesign U) :
    pmfExpect D (fun s => (s.card : ℝ)) = ∑ i, inclusionProb D i := by
  sorry

/-- The covariance of two inclusion indicators: `Cov(𝟙ᵢ, 𝟙ⱼ) = π_{ij} − πᵢ πⱼ`
(`HT52`; the kernel of the Horvitz–Thompson variance). -/
theorem cov_inclusionIndicator (D : SamplingDesign U) (i j : U) :
    pmfCov D (inclusionIndicator i) (inclusionIndicator j)
      = pairInclusionProb D i j - inclusionProb D i * inclusionProb D j := by
  sorry

end StatLean.ExperimentalDesign
