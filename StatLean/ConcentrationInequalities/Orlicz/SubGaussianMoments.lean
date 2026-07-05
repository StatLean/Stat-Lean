import StatLean.ConcentrationInequalities.Orlicz.Attainment
import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Moment growth from the ψ₂ norm

Moment growth from the ψ₂ condition (HDP Prop 2.6.1 (iii)⇒(ii) / Prop
2.6.6(ii)): if $\|X\|_{\psi_2} \le K$ then for all $p \ge 1$
$$ \|X\|_{L^p} \le \sqrt{3}\, K \sqrt{p}, $$
via the even-moment core $\mathbb{E}|X|^{2n} \le 2\,n!\,K^{2n}$ and
`eLpNorm` exponent monotonicity — no Gamma function anywhere.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((iii)⇒(ii)) and Proposition
2.6.6(ii).

**Proof formalization notes.** Constant `C = √3` (frozen numeral
`Real.sqrt 3`; formula: even-moment bound gives `(2·n!)^{1/(2n)}·K·1 ≤
√2·√n·K`, then the reduction `‖X‖_p ≤ ‖X‖_{2⌈p/2⌉}` with `2⌈p/2⌉ ≤ 3p`-slack
absorbed into `√3`). The book's route through `Γ(p/2 + 1)` is avoided: the
even-moment core is the termwise comparison `|x|^{2n} ≤ K^{2n}·n!·e^{(x/K)²}`
(`pow_div_factorial_le_exp`), and real `p ≥ 1` reduces to the even integer
`2⌈p/2⌉` via `MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le` (needs
`[IsProbabilityMeasure μ]`). Statement language: `eLpNorm` at
`ENNReal.ofReal p`; the raw core is a plain lintegral-of-pow bound so the
rpow/coercion conversion is confined to one private helper at proof time.
Named-sorry fallback of this work item: `eLpNorm_le_of_subGaussianNorm_le`
(the real-`p` reduction); the even-moment core must close.

**Bibliographic comments.** Moment growth `‖X‖_p ≍ √p` as the second face of
sub-Gaussianity is classical (Khinchin-type inequalities; Buldygin–Kozachenko
1980); the equivalence bookkeeping follows HDP §2.6 and its Notes.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Even-moment core (HDP §2.6.1): `E|X|^{2n} ≤ 2·n!·K^{2n}` from the
threshold-2 condition, by the termwise bound
`|x|^{2n} ≤ K^{2n}·n!·e^{(x/K)²}` (`pow_div_factorial_le_exp`). -/
theorem lintegral_pow_le_of_lintegral_exp_sq_le_two {X : Ω → ℝ} {μ : Measure Ω}
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * n)) ∂μ
      ≤ ENNReal.ofReal (2 * n.factorial * (K : ℝ) ^ (2 * n)) := by sorry

/-- Even-exponent `eLpNorm` bridge: `‖X‖_{2n} ≤ √2·√n·K` from the even-moment
core (`(2·n!)^{1/(2n)} ≤ √2·√n`). -/
theorem eLpNorm_two_mul_le_of_lintegral_exp_sq_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; eLpNorm regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (n : ℕ)
    -- LEAN-ONLY: n ≥ 1; the p = 0 exponent is excluded (eLpNorm degenerates)
    (hn : 1 ≤ n) :
    MeasureTheory.eLpNorm X (2 * n) μ
      ≤ ENNReal.ofReal (Real.sqrt 2 * Real.sqrt n * (K : ℝ)) := by sorry

/-- **Moment growth** (HDP Proposition 2.6.6(ii), `C = √3`): a sub-Gaussian
norm bound gives `‖X‖_{L^p} ≤ √3·K·√p` for every real `p ≥ 1`. -/
theorem eLpNorm_le_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; exponent monotonicity of eLpNorm needs it
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; eLpNorm regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    {p : ℝ}
    -- USER-INPUT: moment order p ≥ 1; HDP Prop 2.6.6(ii)
    (hp : 1 ≤ p) :
    MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (Real.sqrt 3 * (K : ℝ) * Real.sqrt p) := by sorry

end StatLean.ConcentrationInequalities
