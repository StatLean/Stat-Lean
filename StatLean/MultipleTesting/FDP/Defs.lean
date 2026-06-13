import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# False discovery proportion / rate and family-wise error rate — definitions

Concept-layer definitions for multiple testing (Lu, *Big Data Analysis* ch. 18–19).

Given finitely many hypotheses indexed by `ι`, a set `H₀ : Finset ι` of the *true* null
hypotheses, and a (random) set `R ω : Finset ι` of *rejected* hypotheses, we define:

* `numRejections R ω` — number of rejected hypotheses, `|R ω|`;
* `numFalseRejections H₀ R ω` — number of falsely rejected hypotheses, `|R ω ∩ H₀|`;
* `FDP H₀ R ω` — false discovery proportion `V / (R ∨ 1)` (Lu-BDA §18);
* `FDR H₀ R μ` — false discovery rate `E[FDP]` (Lu-BDA §18);
* `FWER H₀ R μ` — family-wise error rate `P(at least one false rejection)` (Lu-BDA §17).

These are theorem-agnostic; the Benjamini–Hochberg / Holm / knockoff theorems live in sibling
assembly files and consume these definitions. This is a concept-layer foundation.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*}

/-- Number of rejected hypotheses, `|R ω|` (Lu-BDA §18, the `R` of the BH proof). -/
def numRejections (R : Ω → Finset ι) (ω : Ω) : ℕ := (R ω).card

/-- Number of falsely rejected hypotheses — rejected true nulls, `|R ω ∩ H₀|`
(Lu-BDA §18, "# False Positive"). -/
def numFalseRejections [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (ω : Ω) : ℕ :=
  ((R ω) ∩ H₀).card

/-- False discovery proportion `FDP = (# false positives) / (# rejections ∨ 1)` (Lu-BDA §18).
The `max … 1` in the denominator encodes the book's `∨ 1`: with no rejections (`R ω = ∅`) the
numerator is `0` and `FDP = 0`. -/
noncomputable def FDP [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (ω : Ω) : ℝ :=
  (numFalseRejections H₀ R ω : ℝ) / max (numRejections R ω : ℝ) 1

/-- False discovery rate `FDR = E[FDP]` (Lu-BDA §18). -/
noncomputable def FDR [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (μ : Measure Ω) : ℝ :=
  ∫ ω, FDP H₀ R ω ∂μ

/-- Family-wise error rate `FWER = P(R ∩ H₀ ≠ ∅)`: the probability of at least one false
rejection (Lu-BDA §17). Valued in `ℝ≥0∞`. -/
noncomputable def FWER [DecidableEq ι] (H₀ : Finset ι) (R : Ω → Finset ι) (μ : Measure Ω) : ℝ≥0∞ :=
  μ {ω | ((R ω) ∩ H₀).Nonempty}

end StatLean.MultipleTesting
