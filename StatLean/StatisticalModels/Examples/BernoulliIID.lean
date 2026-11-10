import StatLean.StatisticalModels.Identifiability.Transfer
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import StatLean.ForMathlib.UnitInterval

/-!
# Worked instance: the Bernoulli iid model

The simplest end-to-end exercise of the model calculus, doubling as a regression test for the
Core API: the Bernoulli family over the parameter space `{p : ℝ≥0 // p ≤ 1}`, its
identifiability, the success probability as an identified target, and identifiability of the
`n`-fold iid sample model through the replication-iff transfer theorem.

**Reference.** TPE2 §1.1 (the binomial/Bernoulli model as the introductory example of a
statistical model); A. C. Davison, *Statistical Models*, CUP 2003, Ch. 2 (verify §).

**Proof formalization notes.** The family is Mathlib's `bernoulliMeasure true false p`; probability
of the members is its `IsProbabilityMeasure` instance. Identifiability is by evaluating at the event
`{true}` (`bernoulliMeasure_apply_of_mem_of_notMem`); the iid statement is a pure application of
`identifiable_iid_iff` — no new measure theory.

**Bibliographic comments.** The Bernoulli model is Jacob Bernoulli's (*Ars Conjectandi*,
1713); its role as the canonical identifiable one-parameter model is textbook folklore.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.StatisticalModels

open StatLean.PointEstimation

/-- The Bernoulli model: parameter `p ∈ [0,1]`, law of one coin flip on `Bool`. -/
noncomputable def bernoulliFam : {p : ℝ≥0 // p ≤ 1} → Measure Bool :=
  fun p => bernoulliMeasure true false (unitInterval.ofNNReal p.1 p.2)

instance (p : {p : ℝ≥0 // p ≤ 1}) : IsProbabilityMeasure (bernoulliFam p) := by
  unfold bernoulliFam; infer_instance

/-- Point evaluation of the Bernoulli law at the success event. -/
theorem bernoulliFam_apply_true (p : {p : ℝ≥0 // p ≤ 1}) :
    bernoulliFam p {true} = (p.1 : ℝ≥0∞) := by
  rw [bernoulliFam, bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl
    (by simp)]
  simp

/-- The Bernoulli model is identifiable: the success probability is read off the law. -/
theorem identifiable_bernoulliFam : Identifiable bernoulliFam := by
  intro p q hpq
  have h := congrArg (fun ν : Measure Bool => ν {true}) hpq
  simp only [bernoulliFam_apply_true] at h
  exact Subtype.ext (ENNReal.coe_inj.mp h)

/-- The success probability is an identified target of the Bernoulli model. -/
theorem identifiesTarget_bernoulliFam_val :
    IdentifiesTarget bernoulliFam (fun p => (p.1 : ℝ≥0)) :=
  fun _ _ h => congrArg Subtype.val (identifiable_bernoulliFam h)

/-- The `n`-flip iid Bernoulli model is identifiable for `n ≠ 0` — a pure application of the
replication transfer theorem. -/
theorem identifiable_iid_bernoulliFam {n : ℕ}
    -- USER-INPUT: at least one observation; TPE2 §1.1
    (hn : n ≠ 0) :
    Identifiable (iid bernoulliFam n) :=
  (identifiable_iid_iff hn).mpr identifiable_bernoulliFam

end StatLean.StatisticalModels
