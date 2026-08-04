import StatLean.StatisticalModels.Coarsening.Basic
import StatLean.AsymptoticStatistics.Operators.CAR

/-!
# The CAR bridge — MAR missingness is coarsening at random

**C6.** The model-level missingness mechanism of this slice satisfies the semiparametric
layer's coarsening-at-random predicate: for a MAR mechanism, the full-data law disintegrates
over the observed data through a θ-free reconstruction kernel concentrated on the coarsening
fibres —
`IsMAR ρ → IsCoarseningAtRandom missingObserve (fullLaw Q ρ)`
(`AsymptoticStatistics.Operators.CAR.IsCoarseningAtRandom`, imported — never redefined).
This is the bridge that lets the missing-data *models* of this slice consume the
semiparametric observed-data theory (observed tangent spaces, information-loss operator,
influence-function lifts) of vdV §25.6.

This file deliberately imports another area's concept layer (`Operators.CAR`) — the
sanctioned adapter exception, same pattern as `Adapters/`.

**Reference.** D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data," *Ann.
Statist.* **19** (1991), 2244–2253 (`HR91`; CAR as the generalization of MAR); R. D. Gill,
M. J. van der Laan, and J. M. Robins, "Coarsening at random: characterizations, conjectures,
counter-examples," Springer LNS **123** (1997), 255–294 (the disintegration
characterization); vdV §25.6.

**Proof formalization notes.** The reconstruction kernel is glued by `Kernel.piecewise` on
the clopen observed event `{o | o.2.1 = true}`: on the complete-case slice the full datum is
recovered deterministically (`(x, r, ry) ↦ (x, ry, true)`); on the incomplete slice the
outcome is redrawn from the conditional law of `Y` given `X` under `Q` (`condDistrib`, whence
the `StandardBorelSpace`/`Nonempty` instance hypotheses) — MAR is exactly what makes the
`Y ∣ X, R = 0` conditional equal the `Y ∣ X` conditional. The bind identity is verified
slice-by-slice against `Ignorability.observedLaw_restrict_true/false`; the fibre condition is
definitional on the deterministic slice and holds by construction on the other. Designated
XL theorem of the batch — the single allowed carry.

**Bibliographic comments.** That MAR is the single-outcome instance of CAR is `HR91`'s
founding observation; the kernel-disintegration formulation is Gill–van der Laan–Robins
(1997), which is also the form the `Operators.CAR` layer fixes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **C6, the CAR bridge** (`HR91`; Gill–van der Laan–Robins 1997; vdV §25.6): a MAR
missingness mechanism makes the coarsening map `missingObserve` coarsening-at-random for the
full-data law — the model-level missing-data slice plugs into the semiparametric
observed-data theory. Designated XL; the batch's single allowed carry. -/
theorem isCoarseningAtRandom_of_isMAR [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q] {ρ : Kernel (𝓧 × ℝ) Bool}
    [IsMarkovKernel ρ]
    -- USER-INPUT: missing at random; Rubin76 §2, HR91
    (hMAR : IsMAR ρ) :
    AsymptoticStatistics.Operators.CAR.IsCoarseningAtRandom
      (missingObserve (𝓧 := 𝓧)) (fullLaw Q ρ) := by
  sorry

end StatLean.StatisticalModels.Coarsening
