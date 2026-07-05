import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Tail-to-expectation conversion for Gaussian-type tails

Layer-cake analytics converting a high-probability bound into an expectation
bound: if a nonnegative random variable $Z$ satisfies
$$ \mathbb{P}(Z > a + b u) \;\le\; 2 e^{-u^2} \qquad \text{for all } u \ge 0, $$
then
$$ \mathbb{E}[Z] \;\le\; a + \sqrt{\pi}\, b. $$
This is the analytic step from the tail form (8.15) of Dudley's inequality
back to the expectation form (8.14), and the last step of the generic
chaining bound (Theorem 8.5.2). Pure real analysis and measure theory; no
process content.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, the Remark 8.1.6 ⇒ Theorem 8.1.5 step (and
§8.5.2, last step of Theorem 8.5.2); the Gaussian tail estimates are §2.5
folklore (cf. Proposition 2.1.2).

**Proof formalization notes.** The constant is exact:
$\int_0^\infty 2 e^{-u^2}\,du = \sqrt{\pi}$ (half of Mathlib's
`integral_gaussian` by evenness), so `E Z ≤ a + √π·b` with `√π` a frozen
symbolic constant (no numeral rounding). The layer-cake step uses
`lintegral_eq_lintegral_meas_lt` on the `ℝ≥0∞` side; the Bochner form
`integral_le_of_tail_le` DERIVES integrability of `Z` from the finiteness of
the lintegral bound (never hypothesizes it). The auxiliary
`integral_exp_neg_mul_sq_Ioi_le` (tail of the Gaussian integral,
$\int_a^\infty e^{-\beta s^2} ds \le e^{-\beta a^2}/(2\beta a)$ via the
$s/a \ge 1$ majorization) is exported for the split-point optimization in
`Chaining/PsiTwoMaximal.lean`. Named-sorry fallback of this work item:
`integral_le_of_tail_le` (the Bochner wrapper), with the `∫⁻` version
`lintegral_ofReal_le_of_tail_le` proved.

**Bibliographic comments.** The layer-cake (Cavalieri) representation of the
expectation is classical measure theory; its use to integrate chaining tail
bounds is standard since Dudley (1967) and is the textbook route in HDP §8.1
and Talagrand, *Upper and Lower Bounds for Stochastic Processes*, Springer
2014, §2.2. Gaussian tail estimates of the form used here go back to
Laplace; see the HDP Chapter 2 Notes.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Gaussian tail integral bound
`∫_a^∞ exp(−β s²) ds ≤ exp(−β a²)/(2 β a)`, via the `s/a ≥ 1` majorization
and the exact antiderivative of `s · exp(−β s²)`. -/
lemma integral_exp_neg_mul_sq_Ioi_le {a β : ℝ}
    -- LEAN-ONLY: positive split point, so the majorization s/a ≥ 1 applies
    (ha : 0 < a)
    -- LEAN-ONLY: positive Gaussian rate; degenerate β ≤ 0 has no finite tail
    (hβ : 0 < β) :
    ∫ x in Set.Ioi a, Real.exp (-β * x ^ 2)
      ≤ Real.exp (-β * a ^ 2) / (2 * β * a) := by sorry

/-- Exact half-Gaussian integral `∫_0^∞ 2 exp(−u²) du = √π` (halved
`integral_gaussian` by evenness). -/
lemma integral_exp_neg_sq_Ioi_le_sqrt_pi :
    ∫ u in Set.Ioi (0 : ℝ), 2 * Real.exp (-u ^ 2) = Real.sqrt Real.pi := by sorry

/-- **Tail-to-expectation, lintegral form** (HDP §8.1, the Remark 8.1.6 ⇒
Theorem 8.1.5 step): a Gaussian-type tail at thresholds `a + b·u` integrates
to `∫⁻ Z ≤ a + √π·b`, via the layer-cake formula
`lintegral_eq_lintegral_meas_lt` and the substitution `s = a + b u`. -/
theorem lintegral_ofReal_le_of_tail_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability for the layer-cake formula
    (hZm : AEMeasurable Z μ)
    -- LEAN-ONLY: nonnegativity of the supremand being integrated; HDP §8.1
    (hZ0 : 0 ≤ᵐ[μ] Z)
    {a b : ℝ}
    -- LEAN-ONLY: nonnegative threshold offsets (true at every call site)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    -- USER-INPUT: Gaussian-type high-probability bound; HDP §8.1, Eq (8.15)
    (htail : ∀ u : ℝ, 0 ≤ u →
      μ {ω | a + b * u < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2))) :
    ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ
      ≤ ENNReal.ofReal (a + Real.sqrt Real.pi * b) := by sorry

/-- **Tail-to-expectation, Bochner form**: `E Z ≤ a + √π·b`. Integrability of
`Z` is DERIVED from the finite lintegral bound of
`lintegral_ofReal_le_of_tail_le` — not hypothesized. -/
theorem integral_le_of_tail_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability for the layer-cake formula
    (hZm : AEMeasurable Z μ)
    -- LEAN-ONLY: nonnegativity of the supremand being integrated; HDP §8.1
    (hZ0 : 0 ≤ᵐ[μ] Z)
    {a b : ℝ}
    -- LEAN-ONLY: nonnegative threshold offsets (true at every call site)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    -- USER-INPUT: Gaussian-type high-probability bound; HDP §8.1, Eq (8.15)
    (htail : ∀ u : ℝ, 0 ≤ u →
      μ {ω | a + b * u < Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2))) :
    ∫ ω, Z ω ∂μ ≤ a + Real.sqrt Real.pi * b := by sorry

end StatLean.ConcentrationInequalities
