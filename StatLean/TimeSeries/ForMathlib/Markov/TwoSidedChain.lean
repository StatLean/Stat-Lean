import StatLean.TimeSeries.ForMathlib.Markov.Chain
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Two-sided stationary realization of an invariant Markov kernel

The Mathlib pin supplies Ionescu–Tulcea on `ℕ` (`ProbabilityTheory.Kernel.traj`) but no
Kolmogorov extension over `ℤ`, so a two-sided stationary chain cannot be obtained as a
projective limit. This file takes the **natural-extension route instead, which needs no
extension theorem at all**: on a standard Borel state space the time-reversed transition
kernel exists by *disintegration* (`MeasureTheory.Measure.condKernel`), and the two-sided
chain is realized on the concrete space `S × (ℕ → S) × (ℕ → S)` — time-0 value, forward
trajectory (Ionescu–Tulcea for `κ`), and backward trajectory (Ionescu–Tulcea for the
reverse kernel), conditionally independent given time 0.

The single exported interface is `exists_twoSided_stationary_chain`: every finite window
of the constructed `ℤ`-indexed process has the iterated-`compProd` chain law
`chainWindowLaw κ π k`, uniformly in the starting time. Strict stationarity, the Markov
property, and (for autoregression kernels) innovation extraction are all finite-
dimensional consequences of that one equality family, so consumers never touch the
construction.

**Reference.** Natural extension: Rokhlin (1961); the reverse-kernel construction of a
stationary two-sided Markov chain is classical (e.g. Meyn & Tweedie, *Markov Chains and
Stochastic Stability*, ch. 3 notes). Consumed by `Threshold/TAR.lean`
(`exists_stationary_nlAR_of_invariant`, FY §4.1.1) — the last structurally-blocked debt
of the TimeSeries area.

**Bibliographic comments.** The disintegration input is Mathlib's
`Measure.condKernel` (standard Borel); the one-sided trajectory input is
`ProbabilityTheory.Kernel.traj` (Ionescu–Tulcea).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]

/-- The **stationary pair law** `(X₀, X₁) ∼ π ⊗ₘ κ` of one chain step started from `π`.
Formalizes the two-dimensional marginal of the stationary chain (edge behavior: no
hypotheses — invariance is only needed for the *reversal* results below). -/
noncomputable def pairLaw (κ : ProbabilityTheory.Kernel S S) (π : Measure S) :
    Measure (S × S) := π ⊗ₘ κ

instance (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] : IsProbabilityMeasure (pairLaw κ π) := by
  unfold pairLaw; infer_instance

instance (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] :
    IsProbabilityMeasure ((pairLaw κ π).map Prod.swap) :=
  MeasureTheory.isProbabilityMeasure_map measurable_swap.aemeasurable

/-- The **time-reversed transition kernel**: the disintegration in the *second*
coordinate of the swapped stationary pair law. On a standard Borel space this exists by
`Measure.condKernel`. Formalizes the backward transition probability
`P(X₀ ∈ · | X₁ = x)` of the stationary chain (edge behavior: for non-invariant `π` it is
still a Markov kernel, just not a chain reversal). -/
noncomputable def reverseKernel (κ : ProbabilityTheory.Kernel S S) (π : Measure S)
    [IsFiniteMeasure π] [ProbabilityTheory.IsMarkovKernel κ] :
    ProbabilityTheory.Kernel S S :=
  ((pairLaw κ π).map Prod.swap).condKernel

/-- The **iterated-`compProd` chain window law** on `Fin (k+1) → S`: the law of
`(X₀, …, X_k)` for the chain started from `π`. Formalizes the finite-dimensional
distributions of the stationary chain; `k = 0` is the marginal `π` itself. -/
noncomputable def chainWindowLaw (κ : ProbabilityTheory.Kernel S S) (π : Measure S) :
    (k : ℕ) → Measure (Fin (k + 1) → S)
  | 0 => π.map (fun x _ => x)
  | (k + 1) =>
      ((chainWindowLaw κ π k) ⊗ₘ
          (κ.comap (fun w => w (Fin.last k)) (measurable_pi_apply _))).map
        (fun wx => Fin.snoc wx.1 wx.2)

/-- `chainWindowLaw` is a probability measure.
-- LEAN-ONLY: bookkeeping for the recursion; no scope change -/
theorem isProbabilityMeasure_chainWindowLaw
    (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] (k : ℕ) :
    IsProbabilityMeasure (chainWindowLaw κ π k) := by
  sorry

/-- **Reversal disintegration**: under invariance, the swapped pair law disintegrates
through `reverseKernel` with first marginal `π` again.
-- USER-INPUT: κ-invariance of π; the defining property of the stationary reversal -/
theorem pairLaw_swap_eq_compProd_reverseKernel
    (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π]
    (hinv : ProbabilityTheory.Kernel.Invariant κ π) :
    (pairLaw κ π).map Prod.swap = π ⊗ₘ reverseKernel κ π := by
  sorry

/-- **Two-sided stationary realization** (natural extension, no Kolmogorov-over-`ℤ`).
Given an invariant probability `π` of a Markov kernel `κ` on a standard Borel space,
there is a probability space carrying a `ℤ`-indexed process every finite window of which
has the stationary chain law — uniformly in the starting time, which packages strict
stationarity, the Markov property and the marginals in one equality family.
-- USER-INPUT: κ-invariance of π; FY §2.1 stationary-solution setting -/
theorem exists_twoSided_stationary_chain
    (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π]
    (hinv : ProbabilityTheory.Kernel.Invariant κ π) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (Y : ℤ → Ω' → S),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (Y t)) ∧
      ∀ (t : ℤ) (k : ℕ),
        μ'.map (fun ω (i : Fin (k + 1)) => Y (t + (i : ℕ)) ω) = chainWindowLaw κ π k := by
  sorry

end StatLean.TimeSeries
