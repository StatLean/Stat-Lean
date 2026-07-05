import StatLean.ConcentrationInequalities.Symmetrization.Rademacher
import StatLean.ConcentrationInequalities.Symmetrization.SignFlip
import StatLean.ConcentrationInequalities.Symmetrization.NormAddMeanZero
import StatLean.ConcentrationInequalities.ForMathlib.IndepTransport

/-!
# Symmetrization (HDP Lemma 6.3.2)

For independent mean-zero random vectors $X_1, \dots, X_N$ in a Banach space
and independent Rademacher signs $\varepsilon_1, \dots, \varepsilon_N$,
$$ \tfrac12\, \mathbb{E}\Bigl\|\sum_{i=1}^N \varepsilon_i X_i\Bigr\|
   \;\le\; \mathbb{E}\Bigl\|\sum_{i=1}^N X_i\Bigr\|
   \;\le\; 2\, \mathbb{E}\Bigl\|\sum_{i=1}^N \varepsilon_i X_i\Bigr\|, $$
stated as two one-sided inequalities with the book's factors `2` exactly. The
signs live on the canonical product extension `μ.prod (signVec N)` (the mixed
public form); the mathematics happens in a canonical core over laws
`ν : Fin N → Measure E` on `Measure.pi ν`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Lemma 6.3.2 (Symmetrization), pp. 180–181.

**Proof formalization notes.** The canonical **upper** bound is stated in
*centered* form with **no mean-zero hypothesis**:
`∫ ‖∑ (yᵢ − ∫ z ∂νᵢ)‖ ≤ 2 ∫ ‖∑ sᵢ • yᵢ‖` — the centering constant cancels in
`Xᵢ − Xᵢ'`, which is why the empirical RHS of Exercise 8.11 is uncentered;
Lemma 6.3.2 (mean-zero: the centering term vanishes) and Exercise 8.11 are
then one-line instantiations, and no mean-zero hypothesis is laundered where
none is needed. Mean zero **is** needed for the lower bound. Proof per book
pp. 180–181: Eq. (6.13) (`NormAddMeanZero`) with the independent copy realized
as a second `Measure.pi ν` factor, the sign flip (`SignFlip`) plus
a.e.-constancy averaging over `signVec`, then the triangle inequality and
marginalization along `measurePreserving_fst`/`snd`. Mixed public forms follow
by the `ForMathlib/IndepTransport` wrappers. Constants: `2` and `2`, exactly
as the book. Degenerate case: both mixed forms are true and provable at
`N = 0` (empty sums; no `NeZero` hypotheses). Named-sorry fallback of this
work item: `symmetrization_lower_pi` (the upper direction — the one Ex 8.11
and Lemma 6.6.2 consume — fully proven, mixed forms derived).

**Bibliographic comments.** Symmetrization goes back to P. Lévy; the modern
two-sided Banach-space form is due to J.-P. Kahane and is often called the
Kahane symmetrization lemma (Kahane, *Some Random Series of Functions*, 1968;
Ledoux–Talagrand, *Probability in Banach Spaces*, 1991, Lemma 6.3); see HDP
§6.3 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Symmetrization, upper bound, canonical centered form** (HDP §6.3,
Lemma 6.3.2): over the product of the laws `νᵢ`, the expected norm of the
*centered* sum is at most twice the expected norm of the sign-randomized
(uncentered) sum. No mean-zero hypothesis — the centering constant cancels in
the difference of two independent copies. -/
theorem symmetrization_upper_pi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ}
    (ν : Fin N → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    -- USER-INPUT: per-coordinate integrability (book's E‖Xᵢ‖ < ∞); HDP §6.3 Lemma 6.3.2
    (h_int : ∀ i, Integrable id (ν i)) :
    ∫ y, ‖∑ i, (y i - ∫ z, z ∂(ν i))‖ ∂(Measure.pi ν)
      ≤ 2 * ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N)) := by
  sorry

/-- **Symmetrization, lower bound, canonical form** (HDP §6.3, Lemma 6.3.2):
for mean-zero laws, the expected norm of the sign-randomized sum is at most
twice the expected norm of the plain sum. Named-sorry debt candidate of this
work item. -/
theorem symmetrization_lower_pi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ}
    (ν : Fin N → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    -- USER-INPUT: per-coordinate integrability; HDP §6.3 Lemma 6.3.2
    (h_int : ∀ i, Integrable id (ν i))
    -- USER-INPUT: mean zero; HDP §6.3 Lemma 6.3.2
    (h_mean : ∀ i, ∫ z, z ∂(ν i) = 0) :
    ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N))
      ≤ 2 * ∫ y, ‖∑ i, y i‖ ∂(Measure.pi ν) := by
  sorry

/-- **Symmetrization, upper bound, mixed public form** (HDP §6.3,
Lemma 6.3.2): `E‖∑ Xᵢ‖ ≤ 2 E‖∑ εᵢXᵢ‖` for independent mean-zero `Xᵢ` on an
abstract sample space, with the signs as the second coordinate of the product
extension `μ.prod (signVec N)`. -/
theorem symmetrization_upper {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability (book's E‖Xᵢ‖ < ∞); HDP §6.3 Lemma 6.3.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.3 Lemma 6.3.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.3 Lemma 6.3.2
    (hX_indep : iIndepFun X μ) :
    ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ 2 * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) := by
  sorry

/-- **Symmetrization, lower bound, mixed public form** (HDP §6.3,
Lemma 6.3.2; the book's `½E‖∑εX‖ ≤ E‖∑X‖` rearranged):
`E‖∑ εᵢXᵢ‖ ≤ 2 E‖∑ Xᵢ‖`. -/
theorem symmetrization_lower {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.3 Lemma 6.3.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.3 Lemma 6.3.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.3 Lemma 6.3.2
    (hX_indep : iIndepFun X μ) :
    ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N))
      ≤ 2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  sorry

end StatLean.ConcentrationInequalities
