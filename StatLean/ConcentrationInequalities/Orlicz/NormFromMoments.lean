import StatLean.ConcentrationInequalities.Orlicz.Basic
import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# ψ₂ norm from moment growth

The converse moment direction (HDP Prop 2.6.1 (ii)⇒(iii)): if
$\|X\|_{L^p} \le K\sqrt{p}$ for all $p \ge 1$, then
$$ \|X\|_{\psi_2} \le 2\sqrt{e}\, K, $$
by the exponential-series / geometric-sum argument
$\mathbb{E}\,e^{\lambda^2 X^2} = \sum_n \lambda^{2n}\,\mathbb{E}X^{2n}/n!$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((ii)⇒(iii)).

**Proof formalization notes.** Constant `K₃ = 2√e·K₂` book-exact (frozen as
`ENNReal.ofReal (2 * Real.sqrt (Real.exp 1))` — the one constant in this
cluster not encodable as `NNReal.sqrt` of a rational; formula: at
`λ² = 1/(4eK₂²)` the series has geometric ratio `2eλ²K₂² = 1/2`, so it sums
to `2`). The tsum/lintegral swap is `MeasureTheory.lintegral_tsum` +
`ENNReal.ofReal_tsum_of_nonneg`; the factorial lower bound `n! ≥ (n/e)^n` is
the ForMathlib brick `pow_div_exp_pow_le_factorial`. The moment hypothesis is
consumed only at even integers `p = 2n` through the unpacking helper
`lintegral_pow_le_of_eLpNorm_le`, so the rpow/coercion conversion is confined
there. Named-sorry fallback of this work item:
`subGaussianNorm_le_of_eLpNorm_le` (the tsum/geometric-series swap), with the
unpacking helper closed.

**Bibliographic comments.** The series argument converting moment growth into
square-exponential integrability is classical (Khinchin; Buldygin–Kozachenko
1980); constant tracking follows HDP §2.6 and its end-of-chapter Notes.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `eLpNorm` unpacking at even integers: `‖X‖_{2n} ≤ K·√(2n)` gives the
plain even-moment bound `E X^{2n} ≤ (K·√(2n))^{2n} = K^{2n}·(2n)^n`. -/
lemma lintegral_pow_le_of_eLpNorm_le {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; eLpNorm-unpacking regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0} {n : ℕ}
    -- LEAN-ONLY: n ≥ 1; matches the p ≥ 1 range of the moment hypothesis
    (hn : 1 ≤ n)
    -- USER-INPUT: L^{2n} moment bound ‖X‖_{2n} ≤ K√(2n); HDP Prop 2.6.1(ii)
    (h : MeasureTheory.eLpNorm X (2 * n) μ
      ≤ ENNReal.ofReal ((K : ℝ) * Real.sqrt (2 * n))) :
    ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * n)) ∂μ
      ≤ ENNReal.ofReal ((K : ℝ) ^ (2 * n) * (2 * n : ℝ) ^ n) := by sorry

/-- **Norm from moments** (HDP Proposition 2.6.1 (ii)⇒(iii), `K₃ = 2√e·K₂`
book-exact): moment growth `‖X‖_p ≤ K√p` for all `p ≥ 1` bounds the
sub-Gaussian norm by `2√e·K`. -/
theorem subGaussianNorm_le_of_eLpNorm_le
    -- LEAN-ONLY: probability measure; the geometric series sums against μ(univ) = 1
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; series/lintegral-swap regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive moment scale; HDP Prop 2.6.1(ii)
    (hK : 0 < K)
    -- USER-INPUT: moment growth ‖X‖_p ≤ K√p for all p ≥ 1; HDP Prop 2.6.1(ii)
    (hmom : ∀ p : ℝ, 1 ≤ p →
      MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal ((K : ℝ) * Real.sqrt p)) :
    subGaussianNorm X μ
      ≤ ENNReal.ofReal (2 * Real.sqrt (Real.exp 1) * (K : ℝ)) := by sorry

end StatLean.ConcentrationInequalities
