import StatLean.StatisticalLearning.Core.Defs
import Mathlib.Probability.Independence.Basic

/-!
# The i.i.d. sample law — coordinate structure and unbiasedness

Working lemmas about `sampleLaw D n = Measure.pi (fun _ => D)`: the coordinate
evaluations are measure-preserving and jointly independent (the Lean form of
"`S ∼ D^m` i.i.d.", SSBD §2.1), the empirical risk of a fixed hypothesis is
measurable in the sample, unbiased for the true risk (the "preliminary
observation" of SSBD p. 33), and bounded when the loss is bounded.

**Reference.** SSBD §2.1, §4.2 (p. 33). Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** The independence/measure-preservation content is
Mathlib's (`ProbabilityTheory.iIndepFun_pi`, `Measure.pi` marginals); this file
only specializes it to the `sampleLaw` spelling so downstream files never touch
`Measure.pi` directly. Unbiasedness `E_{S∼Dⁿ}[L_S(h)] = L_D(h)` needs `1 ≤ n`
(at `n = 0` the LHS is junk `0`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ}

/-- Coordinate evaluation is measure-preserving from `sampleLaw D n` to `D`
(the marginal of `D^n` is `D`; SSBD §2.1). -/
theorem measurePreserving_eval_sampleLaw (i : Fin n) :
    MeasurePreserving (fun s : Sample Z n => s i) (sampleLaw D n) D := by
  sorry

/-- The coordinate evaluations of an i.i.d. sample are jointly independent
(SSBD §2.1, "independently ... distributed"). -/
theorem iIndepFun_eval_sampleLaw :
    iIndepFun (fun (i : Fin n) (s : Sample Z n) => s i) (sampleLaw D n) := by
  sorry

/-- Measurability of the empirical risk of a fixed hypothesis in the sample
(LEAN-ONLY regularity; SSBD Remark 3.1 supplies measurability of the loss). -/
theorem measurable_empRisk {ℓ : H → Z → ℝ} {h : H}
    -- USER-INPUT: measurability of the loss of `h`; SSBD Remark 3.1
    (hmeas : Measurable (ℓ h)) :
    Measurable fun s : Sample Z n => empRisk ℓ s h := by
  sorry

/-- **Unbiasedness of the empirical risk** (SSBD p. 33, "the expected value of
`L_S(h)` is `L_D(h)`"): for `1 ≤ n`, `E_{S∼Dⁿ}[L_S(h)] = L_D(h)`. -/
theorem integral_empRisk {ℓ : H → Z → ℝ} {h : H}
    -- USER-INPUT: integrability of the loss of `h`; SSBD Remark 3.1 (implicit)
    (hint : Integrable (ℓ h) D)
    -- USER-INPUT: at least one example; SSBD §2.1 (implicit in `S ≠ ∅`)
    (hn : 1 ≤ n) :
    ∫ s, empRisk ℓ s h ∂(sampleLaw D n) = risk D ℓ h := by
  sorry

/-- Pointwise bounds on the empirical risk from bounds on the loss
(LEAN-ONLY convenience; used throughout the finite-class and Rademacher
lanes). -/
theorem empRisk_mem_Icc {ℓ : H → Z → ℝ} {h : H} {a b : ℝ}
    -- USER-INPUT: the loss of `h` has range in `[a,b]`; SSBD §4.2 / Ex. 4.2
    (hab : ∀ z, ℓ h z ∈ Set.Icc a b)
    -- LEAN-ONLY: `1 ≤ n` (at `n = 0` the empirical risk is junk `0`)
    (hn : 1 ≤ n)
    (s : Sample Z n) :
    empRisk ℓ s h ∈ Set.Icc a b := by
  sorry

/-- Bounds on the true risk from bounds on the loss (LEAN-ONLY convenience). -/
theorem risk_mem_Icc {ℓ : H → Z → ℝ} {h : H} {a b : ℝ}
    -- USER-INPUT: the loss of `h` has range in `[a,b]`; SSBD §4.2 / Ex. 4.2
    (hab : ∀ z, ℓ h z ∈ Set.Icc a b)
    -- LEAN-ONLY: measurability, so that the risk integral is genuine
    (hmeas : Measurable (ℓ h)) :
    risk D ℓ h ∈ Set.Icc a b := by
  sorry

/-- Nonnegativity of the true risk for a nonnegative loss (LEAN-ONLY; SSBD's
losses take values in `ℝ₊`, §3.2.1). Holds without integrability (junk `0`). -/
theorem risk_nonneg {ℓ : H → Z → ℝ} {h : H}
    -- USER-INPUT: nonnegative loss; SSBD §3.2.1 (`ℓ : 𝓗 × Z → ℝ₊`)
    (hpos : ∀ z, 0 ≤ ℓ h z) :
    0 ≤ risk D ℓ h := by
  sorry

/-- The best-in-class risk is a lower bound: `bestRisk ≤ risk g` for `g ∈ 𝓗`,
provided the risk image is bounded below (LEAN-ONLY `sInf` regularity;
nonnegative losses give `BddBelow` via `risk_nonneg`). -/
theorem bestRisk_le_risk {𝓗 : Set H} {ℓ : H → Z → ℝ} {g : H}
    (hg : g ∈ 𝓗)
    -- LEAN-ONLY: bounded-below risk image (from loss nonnegativity)
    (hbdd : BddBelow (risk D ℓ '' 𝓗)) :
    bestRisk D 𝓗 ℓ ≤ risk D ℓ g := by
  sorry

end StatLean.StatisticalLearning
