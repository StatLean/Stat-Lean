import StatLean.ConcentrationInequalities.Orlicz.Attainment

/-!
# Sub-exponential tail bound from the ψ₁ norm

The ψ₁ tail bound: if $\mathbb{E}\exp(|X|/K) \le 2$ (in particular if
$\|X\|_{\psi_1} \le K$), then for every $t \ge 0$
$$ \mathbb{P}\bigl(|X| \ge t\bigr) \le 2\exp(-t/K). $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.8.1 ((iii)⇒(i)) and §2.8.2.

**Proof formalization notes.** Constant `c = 1` in the exponent (frozen
numeral `1`, invisible in the statement). **Documented deviation:** direct
Markov on `exp(|X|/K)` (event identity `{t ≤ |X|} = {e^{t/K} ≤ e^{|X|/K}}`,
then `mul_meas_ge_le_lintegral₀`) gives `c = 1`, sharper than the book's
route through property (iv), which yields `K₁ = 3K₃`. Raw core for arbitrary
measures; the norm-facing wrapper derives the threshold-2 condition via the
attainment lemma and hence assumes `[IsProbabilityMeasure μ]`. Tail events
use the ≤-form `μ {ω | t ≤ |X ω|}` with `ENNReal.ofReal` right-hand side (the
`SubGaussian/TailBounds.lean` carrier convention). Named-sorry fallback of
this work item: `measure_abs_ge_le_of_lintegral_exp_abs_le_two` (only if the
Markov event-equality resists; expected to close fully).

**Bibliographic comments.** Exponential tails from exponential moments is
Markov's inequality in its oldest clothing (Bernstein 1924, Chernoff 1952);
the ψ₁ packaging follows HDP §2.8 and its end-of-chapter Notes.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Raw core (HDP Prop 2.8.1 (iii)⇒(i); direct Markov, `c = 1` — sharper
than the book's `K₁ = 3K₃`, see module docstring): the threshold-2 condition
gives the two-sided exponential tail. -/
theorem measure_abs_ge_le_of_lintegral_exp_abs_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.8.1(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / (K : ℝ))) := by sorry

/-- ψ₁-tail bridge (HDP §2.8.2, constant `c = 1`): a sub-exponential norm
bound gives the two-sided exponential tail. -/
theorem measure_abs_ge_le_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-inequality regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP §2.8.2
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP §2.8.2
    (h : subExponentialNorm X μ ≤ K)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.8.1(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / (K : ℝ))) := by sorry

end StatLean.ConcentrationInequalities
