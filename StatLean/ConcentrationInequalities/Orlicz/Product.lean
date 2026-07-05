import StatLean.ConcentrationInequalities.Orlicz.Basic
import StatLean.ConcentrationInequalities.Orlicz.Generators
import StatLean.ConcentrationInequalities.Orlicz.Attainment

/-!
# Sub-Gaussian / sub-exponential product calculus

The two product lemmas of HDP §2.8:
$$ \bigl\|X^2\bigr\|_{\psi_1} = \|X\|_{\psi_2}^2
   \qquad \text{(Lemma 2.8.5, exact equality)}, $$
$$ \|XY\|_{\psi_1} \le \|X\|_{\psi_2}\,\|Y\|_{\psi_2}
   \qquad \text{(Lemma 2.8.6, constant 1)}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Lemma 2.8.5 and Lemma 2.8.6.

**Proof formalization notes.** Both constants are `1` (book-exact; the
book's "check!" in 2.8.5 confirmed — the integrands
`ψ₁(|X²|/k²)` and `ψ₂(|X|/k)` are *literally equal* after `sq_abs`/`div_pow`
rewrites, so 2.8.5 is an exact gauge-set bijection
`K ∈ orliczSet ψ₁ X² ↔ NNReal.sqrt K ∈ orliczSet ψ₂ X`; hence no
hypotheses). The `ℝ≥0∞` squaring of the `⨅` is done by two `≤`-proofs using
the ε-free witness extraction `exists_mem_orliczSet_lt_of_orliczNorm_lt`
rather than an `OrderIso`. For 2.8.6, `hXfin`/`hYfin` (norm ≠ ⊤) are the
book's "X and Y are sub-Gaussian" inputs; the zero-norm edge (`0 · ⊤` in
`ℝ≥0∞`) is handled by case split on `orliczNorm_eq_zero_iff` (X = 0 a.e. ⇒
XY = 0 a.e.); the pointwise chain is Young's split
`|xy|/(ab) ≤ (x/a)²/2 + (y/b)²/2` followed by AM–GM
`e^{u+v} ≤ (e^{2u} + e^{2v})/2` (inline `nlinarith`). Named-sorry fallback of
this work item: `subExponentialNorm_sq` (the `ℝ≥0∞` biInf-squaring
gymnastics); Lemma 2.8.6 must close.

**Bibliographic comments.** The ψ₂–ψ₁ product/squaring calculus is the
standard Orlicz-space Hölder inequality specialized to conjugate Young
functions (Rao–Ren, *Theory of Orlicz Spaces*, 1991, §IV); the constant-1
formulation follows HDP §2.8 (Notes).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Lemma 2.8.5** (HDP; exact, no hypotheses): `‖X²‖_{ψ₁} = ‖X‖_{ψ₂}²` —
the gauge sets correspond exactly under `K ↦ K²` since the integrands are
literally equal. -/
theorem subExponentialNorm_sq (X : Ω → ℝ) (μ : Measure Ω) :
    subExponentialNorm (fun ω => (X ω) ^ 2) μ = (subGaussianNorm X μ) ^ 2 := by
  sorry

/-- **Lemma 2.8.6** (HDP; constant 1): the product of two sub-Gaussian
variables is sub-exponential, `‖XY‖_{ψ₁} ≤ ‖X‖_{ψ₂}·‖Y‖_{ψ₂}`. -/
theorem subExponentialNorm_mul_le {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; gauge-condition regularity
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; gauge-condition regularity
    (hY : AEMeasurable Y μ)
    -- USER-INPUT: X sub-Gaussian (finite ψ₂ norm); HDP Lemma 2.8.6 hypothesis
    (hXfin : subGaussianNorm X μ ≠ ⊤)
    -- USER-INPUT: Y sub-Gaussian (finite ψ₂ norm); HDP Lemma 2.8.6 hypothesis
    (hYfin : subGaussianNorm Y μ ≠ ⊤) :
    subExponentialNorm (fun ω => X ω * Y ω) μ
      ≤ subGaussianNorm X μ * subGaussianNorm Y μ := by sorry

end StatLean.ConcentrationInequalities
