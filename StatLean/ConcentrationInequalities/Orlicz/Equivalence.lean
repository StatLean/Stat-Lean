import StatLean.ConcentrationInequalities.Orlicz.SubGaussianTail
import StatLean.ConcentrationInequalities.Orlicz.TailToNorm
import StatLean.ConcentrationInequalities.Orlicz.SubGaussianMoments
import StatLean.ConcentrationInequalities.Orlicz.NormFromMoments

/-!
# Proposition 2.6.1 — the sub-Gaussian equivalence cycle, composite arrows

Assembly file for the citable composite arrows of the sub-Gaussian
equivalence not stated elsewhere:
$$ \text{(i)} \Rightarrow \text{(ii)}: \quad
   \mathbb{P}(|X|\ge t) \le 2e^{-t^2/K_1^2}
   \implies \|X\|_{L^p} \le 3K_1\sqrt{p} \ (p \ge 1), $$
$$ \text{(iv)} \Rightarrow \text{(i)}: \quad
   \mathbb{E}e^{\lambda X} \le e^{K_4^2\lambda^2}
   \implies \mathbb{P}(|X|\ge t) \le 2e^{-t^2/(2K_4)^2}. $$

The full HDP Proposition 2.6.1 cycle in this development:
(i)⇒(iii) is `TailToNorm.lean` (`K₃ = √3·K₁`, direct layer cake);
(iii)⇒(i) is `SubGaussianTail.lean` (`K₁ = K₃`);
(iii)⇒(ii) is `SubGaussianMoments.lean` (`C = √3`);
(ii)⇒(iii) is `NormFromMoments.lean` (`K₃ = 2√e·K₂`);
(iii)⇒(iv) is `SubGaussianMGF.lean` (`K₄ = √(3/2)·K₃`);
(iv)⇒(i) is here (`K₁ = 2K₄`). Proposition 2.6.6 is the quartet of
norm-instantiated wrappers B1 (tail), (ii) (moments), (iv) (MGF, B2).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((i)⇒(ii) and (iv)⇒(i)) and
Proposition 2.6.6.

**Proof formalization notes.** Composite constants, both book-exact:
(i)⇒(ii) is `3·K₁` (formula `√3·√3·K₁` from (i)⇒(iii) then (iii)⇒(ii); the
book's `K₂ ≤ 3K₁` exactly); (iv)⇒(i) is `K₁ = 2K₄`, with property (iv)
encoded as `HasSubgaussianMGF X (2·K₄²) μ` (Mathlib proxy convention
`E e^{λX} ≤ e^{cλ²/2}`, so `c = 2K₄²`), the two-sided tail from
`HasSubgaussianMGF.measure_ge_le` on `X` and `−X` (`.neg`) + union bound.
The ψ₁ moment property (HDP Prop 2.8.1(ii), book's Exercise 2.41) is OUT OF
SCOPE — not needed by the batch contract or Theorem 2.9.1. Named-sorry
fallback of the owning work item (shared with `SubGaussianTail.lean`):
`eLpNorm_le_of_tail_le` (this file's composite); the B1 pair must close.

**Bibliographic comments.** The equivalence of tail, moment, and MGF
characterizations of sub-Gaussianity is folklore systematized by
Buldygin–Kozachenko (1980; AMS book 2000); the quantitative five-property
cycle with tracked constants is HDP §2.6 (see its Notes).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- HDP Prop 2.6.1 (i)⇒(ii), composite constant `3K₁` (= book's `K₂ ≤ 3K₁`
exactly): Gaussian tails give moment growth `‖X‖_p ≤ 3K₁√p`. -/
theorem eLpNorm_le_of_tail_le
    -- LEAN-ONLY: probability measure; exponent monotonicity of eLpNorm needs it
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; layer-cake/eLpNorm regularity
    (hX : AEMeasurable X μ)
    {K₁ : ℝ≥0}
    -- USER-INPUT: positive tail scale; HDP Prop 2.6.1(i)
    (hK₁ : 0 < K₁)
    -- USER-INPUT: Gaussian-type two-sided tails at scale K₁; HDP Prop 2.6.1(i)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2)))
    {p : ℝ}
    -- USER-INPUT: moment order p ≥ 1; HDP Prop 2.6.1(ii)
    (hp : 1 ≤ p) :
    MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (3 * (K₁ : ℝ) * Real.sqrt p) := by sorry

/-- HDP Prop 2.6.1 (iv)⇒(i), `K₁ = 2K₄` book-exact (property (iv) encoded as
`HasSubgaussianMGF X (2K₄²)`, i.e. `E e^{λX} ≤ e^{K₄²λ²}`): the MGF bound
gives two-sided Gaussian tails. -/
theorem measure_abs_ge_le_of_hasSubgaussianMGF {X : Ω → ℝ} {μ : Measure Ω}
    {K₄ : ℝ≥0}
    -- USER-INPUT: MGF bound E e^{λX} ≤ e^{K₄²λ²} for all λ; HDP Prop 2.6.1(iv)
    (h : ProbabilityTheory.HasSubgaussianMGF X (2 * K₄ ^ 2) μ)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Prop 2.6.1(i)
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (K₄ : ℝ)) ^ 2)) := by sorry

end StatLean.ConcentrationInequalities
