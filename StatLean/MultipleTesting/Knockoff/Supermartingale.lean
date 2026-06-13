import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.Knockoff.Initial
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.ForMathlib.OrderStatistics

/-!
# Knock-off master inequality (Lu-BDA §19) — the supermartingale core

`knockoff_ratio_stopped_le_one`: `E[V₊(t*)/(1+V₋(t*))] ≤ 1`. The heart of the knock-off proof.

Strategy (maximizing Mathlib reuse — this file is where the martingale construction lives, so the
process/filtration definitions co-evolve with their proofs):

* Reveal the null coordinates in **increasing `|W|`** order; the forward process
  `Yproc n = V₊/(1+V₋)` over the `N₀−n` largest-magnitude nulls is a forward supermartingale,
  with `Yproc 0` = the all-nulls ratio (`knockoff_initial_le`) and `Yproc N₀ = 0`.
* `𝒢rev = Filtration.natural` of `(magnitudes, revealed signs)`; the next sign is independent of
  the past (`KnockoffScore.signs_*`), so `μ[next sign | 𝒢rev n] = ½`
  (`iIndepFun.condExp_natural_ae_eq_of_lt`).
* `supermartingale_nat` reduces the supermartingale to the one-step inequality `step_condExp_le`
  (the single high-risk lemma); `tStar` is a bounded `IsStoppingTime` (`isStoppingTime_hittingBtwn`);
  the proven `supermartingale_integral_stoppedValue_le` gives `E[Y_{t*}] ≤ E[Y₀] ≤ 1`.

The construction (`Yproc`, `𝒢rev`, `tauStar`) and the one-step lemma `step_condExp_le` are authored
here by the prover session, alongside this theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- **Master inequality** (Lu-BDA §19): `E[V₊(t*)/(1+V₋(t*))] ≤ 1`, by exhibiting the
threshold-indexed ratio as a supermartingale (one-step inequality from the conditional `Ber(½)`
sign field) and applying optional stopping (`supermartingale_integral_stoppedValue_le`) plus the
initial bound `knockoff_initial_le`. -/
theorem knockoff_ratio_stopped_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) :
    ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ ≤ 1 := by
  sorry

end StatLean.MultipleTesting
