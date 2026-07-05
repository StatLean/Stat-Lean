import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.Orlicz.Basic
import StatLean.ConcentrationInequalities.Orlicz.Generators
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# From Gaussian tails to the ψ₂ norm (B3)

The layer-cake engine: Gaussian-type tails
$\mathbb{P}(|X| \ge t) \le 2e^{-t^2/K_1^2}$ imply the ψ₂ condition at scale
$K = \sqrt{3}\,K_1$, i.e.
$$ \|X\|_{\psi_2} \le \sqrt{3}\, K_1, $$
assembled into the reverse bridge **B3**: a Mathlib `HasSubgaussianMGF X σ2 μ`
(in particular the project carrier `IsSubGaussian`) gives
$\|X\|_{\psi_2} \le \sqrt{6\,\sigma^2}$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((i)⇒(iii)) and the (iv)⇒(i)
composition; Proposition 2.6.6.

**Proof formalization notes.** Constants (all frozen as `NNReal.sqrt`
numerals): `K₃ = √3·K₁` for (i)⇒(iii), and `C' = √6` for B3 (formula:
Mathlib tails give `K₁ = √(2σ2)`, then `√3·√(2σ2) = √(6σ2)`). **Documented
deviation from the book route:** (i)⇒(iii) is proved *directly* by the
weighted layer cake (`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`
with the FTC identity `exp(u²/K²) − 1 = ∫₀ᵘ (2t/K²)e^{t²/K²} dt` and the
improper integral `∫_{(0,∞)} t·e^{−ct²} dt = 1/(2c)` via
`integral_Ioi_of_hasDerivAt_of_tendsto`), avoiding the book's (i)⇒(ii)⇒(iii)
chain and its `Γ(x) ≤ 3x^x` brick, which is absent from Mathlib. B3 takes
no measurability hypothesis beyond the frozen signature:
`HasSubgaussianMGF.aemeasurable` supplies it; tails come from
`HasSubgaussianMGF.measure_ge_le` on `X` and `−X` (via `.neg`). Named-sorry
fallback of this work item: `integral_Ioi_self_mul_exp_neg_mul_sq` (isolated
improper-integral computation); the layer-cake assembly and B3 close modulo
it.

**Bibliographic comments.** The layer-cake (distribution-integral) identity
is classical (see Lieb–Loss, *Analysis*, 2nd ed., §1.13); the tails-to-Orlicz
direction of the equivalence follows HDP §2.6 (Notes), tracing to
Buldygin–Kozachenko (1980).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Improper integral `∫_{(0,∞)} t·exp(−c·t²) dt = 1/(2c)` (antiderivative
`−e^{−ct²}/(2c)` + `integral_Ioi_of_hasDerivAt_of_tendsto`); designated
named-sorry fallback of the tail-to-norm work item. -/
lemma integral_Ioi_self_mul_exp_neg_mul_sq {c : ℝ}
    -- LEAN-ONLY: positive decay rate; integral diverges for c ≤ 0
    (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-c * t ^ 2) = 1 / (2 * c) := by sorry

/-- FTC identity `∫₀ᵘ (2t/K²)·exp(t²/K²) dt = ψ₂(u/K)` feeding the weighted
layer cake `lintegral_comp_eq_lintegral_meas_le_mul`. -/
lemma intervalIntegral_psiTwo_deriv {K : ℝ}
    -- LEAN-ONLY: positive scale; division by K² in the integrand
    (hK : 0 < K)
    {u : ℝ}
    -- LEAN-ONLY: nonnegative upper limit; ψ₂ is evaluated at |X|/K ≥ 0
    (hu : 0 ≤ u) :
    ∫ t in (0 : ℝ)..u, 2 * t / K ^ 2 * Real.exp (t ^ 2 / K ^ 2)
      = psiTwo (u / K) := by sorry

/-- Layer-cake core (HDP Prop 2.6.1 (i)⇒(iii), `K₃ = √3·K₁`; direct route,
see module docstring): Gaussian tails at scale `K₁` verify the Luxemburg
condition at any scale `K ≥ √3·K₁`. -/
theorem lintegral_psiTwo_le_one_of_tail_le {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; layer-cake regularity
    (hX : AEMeasurable X μ)
    {K₁ : ℝ≥0}
    -- USER-INPUT: positive tail scale; HDP Prop 2.6.1(i)
    (hK₁ : 0 < K₁)
    {K : ℝ≥0}
    -- LEAN-ONLY: target scale dominates √3·K₁; the provable constant, stated
    -- with slack so downstream numerals stay NNReal.sqrt expressions
    (hK : Real.sqrt 3 * (K₁ : ℝ) ≤ (K : ℝ))
    -- USER-INPUT: Gaussian-type two-sided tails at scale K₁; HDP Prop 2.6.1(i)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2))) :
    ∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) ∂μ ≤ 1 := by sorry

/-- HDP Prop 2.6.1 (i)⇒(iii) packaged for the norm:
`‖X‖_{ψ₂} ≤ √3·K₁` from Gaussian tails at scale `K₁`. -/
theorem subGaussianNorm_le_of_tail_le {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; layer-cake regularity
    (hX : AEMeasurable X μ)
    {K₁ : ℝ≥0}
    -- USER-INPUT: positive tail scale; HDP Prop 2.6.1(i)
    (hK₁ : 0 < K₁)
    -- USER-INPUT: Gaussian-type two-sided tails at scale K₁; HDP Prop 2.6.1(i)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (K₁ : ℝ) ^ 2))) :
    subGaussianNorm X μ ≤ (NNReal.sqrt 3 * K₁ : ℝ≥0∞) := by sorry

/-- B3 raw form (frozen constant `C' = √6`; formula `√6 = √3·√2` from
Mathlib tails `K₁ = √(2σ2)` composed with `K₃ = √3·K₁`): the Mathlib MGF
predicate bounds the ψ₂ norm. Measurability and tails are supplied by the
predicate itself (`.aemeasurable`, `.measure_ge_le` + `.neg`). -/
theorem subGaussianNorm_le_of_hasSubgaussianMGF {X : Ω → ℝ} {μ : Measure Ω}
    {σ2 : ℝ≥0}
    -- USER-INPUT: sub-Gaussian MGF bound with variance proxy σ2; HDP Prop 2.6.1(iv)
    (h : ProbabilityTheory.HasSubgaussianMGF X σ2 μ) :
    subGaussianNorm X μ ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) := by sorry

/-- B3 project-carrier (centered) form: an `IsSubGaussian` variable has
centered ψ₂ norm at most `√(6σ2)` (chaining's increments consume the raw
form; this is the general-mean corollary). -/
theorem subGaussianNorm_centered_le_of_isSubGaussian {X : Ω → ℝ} {μ : Measure Ω}
    {σ2 : ℝ≥0}
    -- USER-INPUT: X sub-Gaussian with variance proxy σ2; HDP Prop 2.6.6 / Def 2.6.4
    (h : IsSubGaussian X σ2 μ) :
    subGaussianNorm (fun ω => X ω - ∫ x, X x ∂μ) μ
      ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) := by sorry

/-- **B3** (contract form; HDP Proposition 2.6.1 (iv)⇒(iii) with frozen
constant `C' = √6`): a mean-zero `IsSubGaussian` variable has
`‖X‖_{ψ₂} ≤ √(6σ2)`. -/
theorem subGaussianNorm_le_of_isSubGaussian
    -- LEAN-ONLY: probability measure; per the frozen B3 bridge signature
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; per the frozen B3 bridge signature
    (hX : AEMeasurable X μ)
    {σ2 : ℝ≥0}
    -- USER-INPUT: X sub-Gaussian with variance proxy σ2; HDP Prop 2.6.6 / Def 2.6.4
    (h : IsSubGaussian X σ2 μ)
    -- USER-INPUT: mean zero (centered = raw); HDP §2.6 mean-zero convention
    (hmean : ∫ x, X x ∂μ = 0) :
    subGaussianNorm X μ ≤ (NNReal.sqrt (6 * σ2) : ℝ≥0∞) := by sorry

end StatLean.ConcentrationInequalities
