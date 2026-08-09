import StatLean.StatisticalLearning.PACBayes.Defs
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The change-of-measure inequality (Donsker–Varadhan, discrete)

The engine of every PAC-Bayes bound (SSBD Eq. (31.2)): for probability
measures `Q ≪ P` on a countable index and any functional `f`,
`E_Q[f] ≤ D(Q‖P) + log E_P[e^f]`.

**Reference.** SSBD §31.1, Eq. (31.2) ("change of measure + Jensen").
Transcription: `notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Proved for a countable discrete index (Round-1
scope): write `E_Q[f] − D(Q‖P)` as `E_Q[log(e^f · (dP/dQ))]` on the support of
`Q` and apply Jensen for `log` — all sums, no Radon–Nikodym analysis beyond
the discrete density `k ↦ P{k}/Q{k}`. `klDiv` is Mathlib's ℝ≥0∞-valued KL;
finiteness is a hypothesis (`Q ≪ P` alone does not preclude `D = ∞`, in which
case the inequality is vacuous anyway but the `toReal` junk would corrupt the
statement).
-/

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {ι : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  [Countable ι]

/-- **Change of measure / Donsker–Varadhan upper bound** (SSBD Eq. (31.2)):
for probability measures `Q ≪ P` on a countable discrete index with
`D(Q‖P) < ∞`, and `f` with `Q`-integrable value and `P`-integrable
exponential, `E_Q[f] ≤ D(Q‖P) + log E_P[e^f]`. -/
theorem gibbsAvg_le_klDiv_add_log_integral_exp
    (P Q : Measure ι) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : ι → ℝ)
    -- USER-INPUT: absolute continuity `Q ≪ P`; SSBD §31.1 (implicit in
    -- `D(Q‖P) < ∞` for densities — made explicit here)
    (hac : Q ≪ P)
    -- USER-INPUT: finite KL divergence; SSBD Thm 31.1 (the bound is trivial
    -- otherwise)
    (hkl : klDiv Q P ≠ ⊤)
    -- LEAN-ONLY: `Q`-integrability of `f` (bounded functionals downstream)
    (hf : Integrable f Q)
    -- LEAN-ONLY: `P`-integrability of `e^f` (bounded functionals downstream)
    (hexp : Integrable (fun k => Real.exp (f k)) P) :
    gibbsAvg Q f ≤ (klDiv Q P).toReal +
      Real.log (∫ k, Real.exp (f k) ∂P) := by
  sorry

end StatLean.StatisticalLearning
