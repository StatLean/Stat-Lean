import StatLean.ConcentrationInequalities.Orlicz.Basic
import StatLean.ConcentrationInequalities.Orlicz.Generators

/-!
# Orlicz norm — triangle inequality

The triangle inequality for the general Luxemburg norm,
$$ \|X + Y\|_\psi \le \|X\|_\psi + \|Y\|_\psi, $$
via convexity: if `a` is a gauge for `X` and `b` a gauge for `Y`, then
`a + b` is a gauge for `X + Y` since
$$ \psi\Bigl(\frac{u + v}{a+b}\Bigr)
   \le \frac{a}{a+b}\,\psi\Bigl(\frac{u}{a}\Bigr)
     + \frac{b}{a+b}\,\psi\Bigl(\frac{v}{b}\Bigr). $$
Instances for the ψ₂/ψ₁ generators (first half of the B4 bridge; homogeneity
is `Orlicz/Basic.lean`) and the finite-sum corollary.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Exercise 2.42 (‖·‖_{ψ₂} is a norm) and the display
after Eq. (2.18) in §2.6.1; Exercise 2.43 for the general Orlicz norm.

**Proof formalization notes.** The `ENNReal` inf-addition step
("`⨅ + ⨅ = ⨅` of sums") has no packaged Mathlib lemma on this index; it is
hand-rolled through the ε-free witness pattern
`exists_mem_orliczSet_lt_of_orliczNorm_lt` with explicit case splits on empty
gauge sets (`norm = ⊤` makes the bound trivial). Measurability of ψ and
a.e.-measurability of X, Y are LEAN-ONLY hypotheses: the plain `lintegral` is
not subadditive without measurability of the integrands. Constants: exact
(the triangle inequality carries no constant). Named-sorry fallback of this
work item: `orliczNorm_add_le` itself, with the ψ₂/ψ₁ instances and the
finset-sum corollary derived from it.

**Bibliographic comments.** That the Luxemburg gauge is a norm is Luxemburg's
thesis (Delft, 1955); Vershynin assigns the ψ₂ case as HDP Exercise 2.42. See
also Rao–Ren, *Theory of Orlicz Spaces*, Dekker 1991, §III.3.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Triangle inequality** for the Orlicz norm (HDP Exercise 2.42; B4 part 1):
gauges add along the convexity splitting of ψ. -/
theorem orliczNorm_add_le {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- USER-INPUT: ψ convex on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_conv : ConvexOn ℝ (Set.Ici 0) ψ)
    -- LEAN-ONLY: measurability of ψ; plain lintegral is not subadditive without
    -- measurable integrands, satisfied by both generators, no book scope change
    (hψ_meas : Measurable ψ)
    {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; lintegral-additivity regularity
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; lintegral-additivity regularity
    (hY : AEMeasurable Y μ) :
    orliczNorm ψ (fun ω => X ω + Y ω) μ ≤ orliczNorm ψ X μ + orliczNorm ψ Y μ := by
  sorry

/-- Triangle inequality for the sub-Gaussian norm (B4; HDP Exercise 2.42 /
display after Eq. (2.18) in §2.6.1). -/
theorem subGaussianNorm_add_le {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; inherited from orliczNorm_add_le
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; inherited from orliczNorm_add_le
    (hY : AEMeasurable Y μ) :
    subGaussianNorm (fun ω => X ω + Y ω) μ
      ≤ subGaussianNorm X μ + subGaussianNorm Y μ := by sorry

/-- Triangle inequality for the sub-exponential norm (B4, ψ₁ instance). -/
theorem subExponentialNorm_add_le {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; inherited from orliczNorm_add_le
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; inherited from orliczNorm_add_le
    (hY : AEMeasurable Y μ) :
    subExponentialNorm (fun ω => X ω + Y ω) μ
      ≤ subExponentialNorm X μ + subExponentialNorm Y μ := by sorry

/-- Finite-sum triangle inequality (induction corollary; finiteness
ingredient for `IsSubGaussianVec`). -/
theorem orliczNorm_finset_sum_le {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- USER-INPUT: ψ convex on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_conv : ConvexOn ℝ (Set.Ici 0) ψ)
    -- LEAN-ONLY: measurability of ψ; inherited from orliczNorm_add_le
    (hψ_meas : Measurable ψ)
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of each summand; inherited from orliczNorm_add_le
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) :
    orliczNorm ψ (fun ω => ∑ i ∈ s, X i ω) μ ≤ ∑ i ∈ s, orliczNorm ψ (X i) μ := by
  sorry

end StatLean.ConcentrationInequalities
