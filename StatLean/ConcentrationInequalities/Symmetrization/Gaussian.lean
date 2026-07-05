import StatLean.ConcentrationInequalities.Symmetrization.Symmetrization
import StatLean.ConcentrationInequalities.Symmetrization.Contraction
import StatLean.ConcentrationInequalities.Symmetrization.SymmetricLaw
import StatLean.ConcentrationInequalities.Symmetrization.GaussianVector
import StatLean.ConcentrationInequalities.Symmetrization.GaussianMax

/-!
# Symmetrization with Gaussians (HDP Lemma 6.6.2)

For independent mean-zero random vectors $X_1, \dots, X_N$ in a Banach space
and independent standard Gaussian multipliers $g_1, \dots, g_N$,
$$ \mathbb{E}\Bigl\|\sum_i X_i\Bigr\|
   \;\le\; \sqrt{2\pi}\; \mathbb{E}\Bigl\|\sum_i g_i X_i\Bigr\|
   \qquad\text{and}\qquad
   \mathbb{E}\Bigl\|\sum_i g_i X_i\Bigr\|
   \;\le\; 2\sqrt{2\log(2N)}\; \mathbb{E}\Bigl\|\sum_i X_i\Bigr\|. $$
The Gaussian multipliers live on the product extension `μ.prod (gaussVec N)`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, Lemma 6.6.2 (Symmetrization with
Gaussians), pp. 185–186; the unavoidability of the $\sqrt{\log N}$ factor is
Remark 6.6.3.

**Proof formalization notes.** **Constants.** Upper: we prove the *sharp*
constant $\sqrt{2\pi} = 2\sqrt{\pi/2} \approx 2.5066$, from the exact
$\mathbb{E}|g| = \sqrt{2/\pi}$ (`ForMathlib/GaussianAbsMoment`); the book's
display constant `3` is provided as the headline via `√(2π) ≤ 3`
(`2π ≤ 8 < 9` from `Real.pi_le_four`). Lower: the book's unnamed
`(c/√(log N)) E‖∑gX‖ ≤ E‖∑X‖` is committed to the explicit all-`N ≥ 1` form
with factor `2·√(2 log(2N))` (`2` from Lemma 6.3.2-lower, `√(2 log(2N))` from
`GaussianMax`; the `2N` vs `N` in the log is the documented two-sided
union-bound cost), plus the `N ≥ 2` corollary with factor `4√(log N)` — the
book's `c = 1/4` — via `log(2N) ≤ 2 log N`. **Proof route** (book
pp. 185–186). Upper: Lemma 6.3.2-upper, insert `E|g| = √(2/π)`, Jensen
pointwise (`norm_integral_le_integral_norm` + `integral_smul_const`), then
`(εᵢ|gᵢ|) =ᵈ (gᵢ)` (`SymmetricLaw`). Lower: `(εᵢgᵢ) =ᵈ (gᵢ)`, pointwise
contraction with `a := g` conditionally on `(ω, s)`, factorize with
`integral_prod_mul`, Lemma 6.3.2-lower, and `E max|gᵢ|` (`GaussianMax`).
Triple products `μ ⊗ signVec ⊗ gaussVec` are handled in iterated-integral
style (`integral_prod` twice) — no `Measure.prod` associativity plumbing.
`N = 0` in the all-`N` lower bound is a case split (both sides `0`; `Real.log`
junk makes the constant harmless). Named-sorry fallback of this work item:
`gaussian_symmetrization_lower` (the upper chain with the `√(2π)`/`3`
constants fully proven; the `N ≥ 2` corollary inherits the debt).

**Bibliographic comments.** Gaussian–Rademacher comparison is classical
Banach-space theory: the upper direction and the `√(log N)` loss trace to
unconditionality arguments in Ledoux–Talagrand, *Probability in Banach
Spaces* (1991), §4.2 (where the loss is shown necessary at `ℓ∞^N`); see HDP
§6.6 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Gaussian symmetrization, upper bound, sharp constant** (HDP §6.6,
Lemma 6.6.2): `E‖∑ Xᵢ‖ ≤ √(2π) · E‖∑ gᵢXᵢ‖` — the sharp form of the book's
constant `3`, from the exact `E|g| = √(2/π)`. -/
theorem gaussian_symmetrization_upper_sqrt {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability (book's E‖Xᵢ‖ < ∞); HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ Real.sqrt (2 * Real.pi)
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N)) := by
  sorry

/-- **Gaussian symmetrization, upper bound, book constant** (HDP §6.6,
Lemma 6.6.2): `E‖∑ Xᵢ‖ ≤ 3 · E‖∑ gᵢXᵢ‖`; headline via `√(2π) ≤ 3`
(`Real.pi_le_four`). -/
theorem gaussian_symmetrization_upper {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ 3 * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N)) := by
  sorry

/-- **Gaussian symmetrization, lower bound, explicit constant** (HDP §6.6,
Lemma 6.6.2): `E‖∑ gᵢXᵢ‖ ≤ 2√(2 log(2N)) · E‖∑ Xᵢ‖` for all `N` (both sides
`0` at `N = 0`). Documented deviation: `√(log 2N)` vs the book's `√(log N)`
(two-sided union-bound cost). Named-sorry debt candidate of this work item. -/
theorem gaussian_symmetrization_lower {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))
      ≤ 2 * Real.sqrt (2 * Real.log (2 * N)) * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  sorry

/-- **Gaussian symmetrization, lower bound, book form** (HDP §6.6,
Lemma 6.6.2): for `N ≥ 2`, `E‖∑ gᵢXᵢ‖ ≤ 4√(log N) · E‖∑ Xᵢ‖` — the book's
`(c/√(log N)) E‖∑gX‖ ≤ E‖∑X‖` with explicit `c = 1/4`, via
`log(2N) ≤ 2 log N`. -/
theorem gaussian_symmetrization_lower_log {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ}
    -- USER-INPUT: 2 ≤ N (the book's c/√(log N) form is vacuous at N = 1); HDP §6.6
    (hN : 2 ≤ N)
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))
      ≤ 4 * Real.sqrt (Real.log N) * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  sorry

end StatLean.ConcentrationInequalities
