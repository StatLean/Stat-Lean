import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The pointwise (Birkhoff) ergodic theorem

The Mathlib pin carries the algebraic bookkeeping for `birkhoffSum`/`birkhoffAverage` and
von Neumann's *mean* (L²) ergodic theorem, but no maximal ergodic theorem and no a.e.
convergence statement. This file supplies them, for a measure-preserving map of a
probability space: the maximal ergodic theorem (Garsia's proof), a.e. convergence of
Birkhoff averages to the conditional expectation on the invariant σ-algebra, and the
ergodic corollary (limit = the space mean).

Consumed by `Mixing/LimitTheorems.slln_of_alphaMixing_debt` (FY Prop 2.8), whose closing
wave recorded the four-item build list this file is item (iii) of.

**Reference.** Birkhoff (1931); the maximal-inequality proof is Garsia (1965). FY cite
Doob 1953 / Ibragimov–Linnik 1971 for the mixing SLLN.

**Bibliographic comments.** The invariant σ-algebra and the condexp form follow the
standard modern treatment (e.g. Einsiedler–Ward, *Ergodic Theory*, ch. 2).
-/

open MeasureTheory Filter
open scoped Topology

namespace StatLean.TimeSeries

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- The **invariant σ-algebra** of a self-map: measurable sets with `f ⁻¹' s = s`.
Formalizes the almost-invariant information of the dynamics (edge behavior: for
non-measurable `f` this is still a σ-algebra, just not comparable to the ambient one
through `f`). -/
def invariantSigma (f : α → α) : MeasurableSpace α where
  MeasurableSet' s := MeasurableSet s ∧ f ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, by rw [Set.preimage_compl, hs.2]⟩
  measurableSet_iUnion g hg :=
    ⟨MeasurableSet.iUnion fun i => (hg i).1, by
      simp only [Set.preimage_iUnion]
      exact Set.iUnion_congr fun i => (hg i).2⟩

/-- The invariant σ-algebra is coarser than the ambient one.
-- LEAN-ONLY: needed to state the conditional expectation; no scope change -/
theorem invariantSigma_le (f : α → α) : invariantSigma f ≤ ‹MeasurableSpace α› :=
  fun _ hs => hs.1

/-- **The maximal ergodic theorem** (Garsia): for integrable `g`, the integral of `g`
over the set where some Birkhoff sum is positive is nonnegative.
-- USER-INPUT: measure-preserving dynamics and integrable observable; Birkhoff/Garsia -/
theorem maximal_ergodic (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}, g x ∂μ := by
  sorry

/-- **The pointwise (Birkhoff) ergodic theorem, conditional-expectation form**: for a
measure-preserving `f` on a probability space and integrable `g`, the Birkhoff averages
converge a.e. to the conditional expectation of `g` on the invariant σ-algebra.
-- USER-INPUT: measure-preserving dynamics and integrable observable; Birkhoff 1931 -/
theorem birkhoffAverage_ae_tendsto_condexp [IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) (hfm : Measurable f) {g : α → ℝ}
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f g n x) atTop
      (𝓝 ((μ[g | invariantSigma f]) x)) := by
  sorry

/-- **Birkhoff for an ergodic map**: the averages converge a.e. to the space mean.
-- USER-INPUT: ergodic dynamics and integrable observable; Birkhoff 1931 -/
theorem birkhoffAverage_ae_tendsto_integral [IsProbabilityMeasure μ]
    (hf : Ergodic f μ) (hfm : Measurable f) {g : α → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f g n x) atTop (𝓝 (∫ x, g x ∂μ)) := by
  sorry

end StatLean.TimeSeries
