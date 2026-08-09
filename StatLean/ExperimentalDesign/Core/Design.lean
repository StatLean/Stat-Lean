import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
# Designs: allocations, randomization designs, sampling designs

The two primitive objects of design-based statistics, in their finite Round-1 form:

* an **experimental design** randomly assigns one treatment from a finite set `T` to
  each unit of a finite population `U` — a probability distribution on the
  *allocations* `U → T`;
* a **sampling design** randomly selects a subset of `U` — a probability distribution
  on `Finset U`.

Both are carried by Mathlib's `PMF`, the least-friction finite carrier (no σ-algebra
needed; expectations reduce to finite sums via
`StatLean.ExperimentalDesign.pmfExpect`).  This file fixes the vocabulary —
allocations, treatment arms, arm indicators and arm means, inclusion indicators and
sample means — and proves the deterministic (per-outcome) identities relating them.
Moment computations under specific designs live downstream
(`Randomization/`, `SurveySampling/`).

## Main definitions

* `Allocation`, `RandomizationDesign`, `SamplingDesign` — the carriers.
* `arm`, `armIndicator`, `armMean` — the units receiving treatment `t`, the 0/1
  assignment indicator, and the arm sample mean.
* `inclusionIndicator`, `sampleMean` — the sampling-side analogues.

## Main results

* `sum_arm_card` — arm sizes partition the population size.
* `sum_armIndicator` — each unit is in exactly one arm.
* `armIndicator_mul_armIndicator_of_ne` — arms are mutually exclusive.
* `sum_arm_eq_sum_indicator`, `sum_sample_eq_sum_indicator` — indicator
  representations of arm/sample sums.
* `armMean_eq_sampleMean_arm` — the arm mean is the sample mean of the arm.

**Reference.** R. Mead, *The Design of Experiments*, Cambridge University Press,
1988: random treatment allocation and the allocation indicator random variables,
§9.2 and §9.4 (the `δᵏᵢⱼ` indicators); the completely randomised design and its
treatment groups, §6.2.  (`Mead §9.2`, `Mead §9.4`, `Mead §6.2`.)

**Proof formalization notes.**
* `Allocation U T` is a plain function type and `RandomizationDesign U T = PMF (U → T)`
  a plain `PMF`; both are `abbrev`s so downstream files see through them
  definitionally.
* Indicators are `ℝ`-valued from the start (values `0`/`1`), so moment statements
  need no coercion bookkeeping.
* `armMean` uses `(card)⁻¹ *` with the `(0:ℝ)⁻¹ = 0` convention: the mean over an
  empty arm is `0`.  Statements about arm means under a design carry the replication
  hypothesis (`r t ≠ 0`) that rules the empty case out.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

/-- An **allocation** (treatment assignment): each unit of `U` receives one treatment
from `T` (`Mead §9.2`, random treatment allocation — this is one realisation). -/
abbrev Allocation (U T : Type*) := U → T

/-- A **randomization design**: a probability mass function on allocations.  The
randomization distribution of a designed experiment (`Mead §9.2`). -/
abbrev RandomizationDesign (U T : Type*) := PMF (Allocation U T)

/-- A **sampling design**: a probability mass function on subsets of the population
(the survey-sampling primitive; not covered by Mead, cf. Horvitz–Thompson 1952). -/
abbrev SamplingDesign (U : Type*) := PMF (Finset U)

section Allocation

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-- The **treatment arm** of `t` under allocation `a`: the units assigned to `t`
(`Mead §6.2`, the group of units receiving one treatment). -/
def arm (t : T) (a : Allocation U T) : Finset U :=
  Finset.univ.filter fun i => a i = t

/-- The **assignment indicator** `1{a(i) = t}` as a real number — Mead's `δ`
indicator random variable of the randomization theory (`Mead §9.4`), viewed as a
statistic of the allocation. -/
def armIndicator (t : T) (i : U) (a : Allocation U T) : ℝ :=
  if a i = t then 1 else 0

/-- The **arm mean** of a population quantity `y`: the average of `y` over the units
assigned to `t`.  Edge behaviour: `0` for an empty arm (`(0:ℝ)⁻¹ = 0`). -/
noncomputable def armMean (y : U → ℝ) (t : T) (a : Allocation U T) : ℝ :=
  ((arm t a).card : ℝ)⁻¹ * ∑ i ∈ arm t a, y i

@[simp]
theorem mem_arm_iff {t : T} {a : Allocation U T} {i : U} :
    i ∈ arm t a ↔ a i = t := by
  sorry

/-- Arm sizes partition the population size. -/
theorem sum_arm_card (a : Allocation U T) :
    ∑ t, (arm t a).card = Fintype.card U := by
  sorry

/-- Every unit lies in exactly one arm: the assignment indicators over treatments sum
to one. -/
theorem sum_armIndicator (a : Allocation U T) (i : U) :
    ∑ t, armIndicator t i a = 1 := by
  sorry

/-- Arms are mutually exclusive: indicators of distinct treatments at the same unit
have vanishing product (`Mead §9.4`, the joint properties of the `δ` indicators). -/
theorem armIndicator_mul_armIndicator_of_ne {t s : T}
    -- LEAN-ONLY: distinct treatments; the case `t = s` is the idempotency below
    (hts : t ≠ s) (i : U) (a : Allocation U T) :
    armIndicator t i a * armIndicator s i a = 0 := by
  sorry

/-- Assignment indicators are idempotent (`0/1`-valued). -/
theorem armIndicator_mul_self (t : T) (i : U) (a : Allocation U T) :
    armIndicator t i a * armIndicator t i a = armIndicator t i a := by
  sorry

/-- Indicator representation of a sum over one arm. -/
theorem sum_arm_eq_sum_indicator (y : U → ℝ) (t : T) (a : Allocation U T) :
    ∑ i ∈ arm t a, y i = ∑ i, armIndicator t i a * y i := by
  sorry

/-- The arm size as the sum of assignment indicators. -/
theorem card_arm_eq_sum_indicator (t : T) (a : Allocation U T) :
    ((arm t a).card : ℝ) = ∑ i, armIndicator t i a := by
  sorry

end Allocation

section Sampling

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The **inclusion indicator** `1{i ∈ S}` of a unit in a sample, as a real number
(the survey-sampling analogue of `armIndicator`). -/
def inclusionIndicator (i : U) (s : Finset U) : ℝ :=
  if i ∈ s then 1 else 0

/-- The **sample mean** of a population quantity over a subset.  Edge behaviour: `0`
for the empty sample. -/
noncomputable def sampleMean (y : U → ℝ) (s : Finset U) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ i ∈ s, y i

/-- Inclusion indicators are idempotent (`0/1`-valued). -/
theorem inclusionIndicator_mul_self (i : U) (s : Finset U) :
    inclusionIndicator i s * inclusionIndicator i s = inclusionIndicator i s := by
  sorry

/-- Indicator representation of a sum over the sample. -/
theorem sum_sample_eq_sum_indicator (y : U → ℝ) (s : Finset U) :
    ∑ i ∈ s, y i = ∑ i, inclusionIndicator i s * y i := by
  sorry

/-- The sample size as the sum of inclusion indicators. -/
theorem card_sample_eq_sum_indicator (s : Finset U) :
    ((s.card : ℝ)) = ∑ i, inclusionIndicator i s := by
  sorry

end Sampling

section Bridge

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-- The assignment indicator is the inclusion indicator of the arm. -/
theorem armIndicator_eq_inclusionIndicator (t : T) (i : U) (a : Allocation U T) :
    armIndicator t i a = inclusionIndicator i (arm t a) := by
  sorry

/-- The arm mean is the sample mean of the arm — the bridge along which arm-mean
moments are inherited from sampling-design moments. -/
theorem armMean_eq_sampleMean_arm (y : U → ℝ) (t : T) (a : Allocation U T) :
    armMean y t a = sampleMean y (arm t a) := by
  sorry

end Bridge

end StatLean.ExperimentalDesign
