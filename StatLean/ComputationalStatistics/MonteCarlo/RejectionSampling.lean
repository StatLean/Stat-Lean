import StatLean.ComputationalStatistics.Core.Defs
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability

/-!
# Rejection sampling (the acceptance/rejection method)

The correctness of Gentle's Algorithm 2.1 (ECS §2.1): draw `Y` from a proposal
with density `q`, draw `U ~ U(0,1)` independently, and accept `Y` when
`U ≤ p(Y)/(c·q(Y))`, where `p` is the target density and `c·q` majorizes `p`.
Then

* `rejectionSampling_acceptProb` — the acceptance probability is `1/c`;
* `rejectionSampling_restrict_map` — the accepted-restricted first marginal is
  `c⁻¹ · (ν.withDensity p)` (the workhorse identity);
* `rejectionSampling_conditionalLaw` — **the accepted draw has exactly the
  target law**: `Law(Y | accept) = ν.withDensity p`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.1, Algorithm 2.1 and the correctness display
`Pr(Z ≤ x) = ∫_{−∞}^x p_X(t) dt` on p. 40.  (`ECS §2.1`.)

**Proof formalization notes.**

* Densities are `ℝ≥0∞`-valued against an arbitrary σ-finite base measure `ν`
  (Gentle's remark that the discussion covers mass functions verbatim is then
  automatic: take `ν = Measure.count`).
* The acceptance region is stated in the **multiplicative form**
  `ofReal u * (c * q y) ≤ p y`, which is junk-free at `q y = 0`; it agrees with
  the book's `u ≤ p/(cq)` off the `Q`-null set `{q = 0}`.
* `c ≠ 0` is required for the marginal identity (at `c = 0` the accept region
  is everything and the claim is false); `c ≥ 1` is *derivable* from the
  majorization plus `∫⁻ p dν = 1` and is not assumed.
* The geometric law of the number of trials to first acceptance (ECS §2.1,
  p. 40) is deferred to a later round: it needs the infinite i.i.d. proposal
  stream and a hitting-time construction, orthogonal to the correctness core.

**Bibliographic comments.** The method is von Neumann's ("Various techniques
used in connection with random digits," *NBS Applied Math. Series* **12**
(1951), 36–38); the majorizing-density formulation is standard since
Devroye, *Non-Uniform Random Variate Generation*, Springer, 1986, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

/-- The **uniform distribution on `[0,1]`**: Lebesgue measure restricted to the
unit interval.  The auxiliary randomization of the acceptance step. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance isProbabilityMeasure_uniform01 : IsProbabilityMeasure uniform01 := by
  sorry

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {ν : Measure 𝓧} [SigmaFinite ν]
  {p q : 𝓧 → ℝ≥0∞} {c : ℝ≥0∞}

/-- The **acceptance region** of Algorithm 2.1 (ECS §2.1): the pairs `(y, u)`
with `u·c·q(y) ≤ p(y)`.  Multiplicative form of the book's `u ≤ p(y)/(c·q(y))`;
the two agree wherever `q y ≠ 0`, hence `Q`-a.e. -/
def rejectionAccept (p q : 𝓧 → ℝ≥0∞) (c : ℝ≥0∞) : Set (𝓧 × ℝ) :=
  {yu | ENNReal.ofReal yu.2 * (c * q yu.1) ≤ p yu.1}

/-- The acceptance region is measurable. -/
theorem measurableSet_rejectionAccept
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q) :
    MeasurableSet (rejectionAccept p q c) := by
  sorry

/-- **Accepted-restricted marginal identity**: restricting the joint proposal
`(Y, U) ~ (ν.withDensity q) ⊗ U(0,1)` to the acceptance region, the law of `Y`
is `c⁻¹ · (ν.withDensity p)`.  This is the workhorse behind both the
acceptance probability and the conditional-law theorem. -/
theorem rejectionSampling_restrict_map
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q)
    -- USER-INPUT: the scaled proposal majorizes the target, `p ≤ c·q`; ECS §2.1
    (henv : ∀ y, p y ≤ c * q y)
    -- USER-INPUT: a positive, finite envelope constant; ECS §2.1
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    (((ν.withDensity q).prod uniform01).restrict (rejectionAccept p q c)).map
        Prod.fst
      = c⁻¹ • ν.withDensity p := by
  sorry

/-- **Acceptance probability of rejection sampling** (ECS §2.1, p. 40): the
joint proposal puts mass exactly `1/c` on the acceptance region. -/
theorem rejectionSampling_acceptProb
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q)
    -- USER-INPUT: the target density integrates to one; ECS §2.1
    (hp1 : ∫⁻ z, p z ∂ν = 1)
    -- USER-INPUT: the scaled proposal majorizes the target, `p ≤ c·q`; ECS §2.1
    (henv : ∀ y, p y ≤ c * q y)
    -- USER-INPUT: a positive, finite envelope constant; ECS §2.1
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    ((ν.withDensity q).prod uniform01) (rejectionAccept p q c) = c⁻¹ := by
  sorry

/-- **Rejection sampling returns exactly the target law** (ECS §2.1,
Algorithm 2.1 and the display on p. 40): conditionally on acceptance, the
proposed draw has law `ν.withDensity p`. -/
theorem rejectionSampling_conditionalLaw
    -- LEAN-ONLY: measurability of the target density (regularity)
    (hp : Measurable p)
    -- LEAN-ONLY: measurability of the proposal density (regularity)
    (hq : Measurable q)
    -- USER-INPUT: the target density integrates to one; ECS §2.1
    (hp1 : ∫⁻ z, p z ∂ν = 1)
    -- USER-INPUT: the scaled proposal majorizes the target, `p ≤ c·q`; ECS §2.1
    (henv : ∀ y, p y ≤ c * q y)
    -- USER-INPUT: a positive, finite envelope constant; ECS §2.1
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    (ProbabilityTheory.cond ((ν.withDensity q).prod uniform01)
        (rejectionAccept p q c)).map Prod.fst
      = ν.withDensity p := by
  sorry

end StatLean.ComputationalStatistics
