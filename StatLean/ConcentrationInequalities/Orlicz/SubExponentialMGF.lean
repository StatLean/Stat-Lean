import StatLean.ConcentrationInequalities.SubExponential.Defs
import StatLean.ConcentrationInequalities.Orlicz.Attainment
import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds

/-!
# Restricted-range MGF bound from the ψ₁ norm

The ψ₁ analogue of B2 (HDP Prop 2.8.1 (iii)⇒(iv)): if $\mathbb{E}X = 0$ and
$\|X\|_{\psi_1} \le K$, then
$$ \mathbb{E}\,e^{\lambda X} \le \exp\bigl(4\lambda^2 K^2\bigr)
   \qquad \text{for } |\lambda| \le \tfrac{1}{2K}, $$
with the bridge into the existing project carrier `IsSubExponential` at
parameter $\alpha = 2\sqrt{2}\,K$ — the engine Bernstein 2.9.1 consumes.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.8.1 ((iii)⇒(iv)).

**Proof formalization notes.** Constants: `K₄ = 2K` book-exact (MGF bound
`exp(4λ²K²)` on `|λ| ≤ 1/(2K)`; frozen numerals `4` and `2`); carrier bridge
`α = 2√2·K` exact (frozen `2 * NNReal.sqrt 2 * K`; formula: `4λ²K² = λ²α²/2`
forces `α² = 8K²`, and `1/α = 1/(2√2·K) ≤ 1/(2K)` keeps the range inside the
proven one). The proof splits `E e^{λX} ≤ 1 + λ·EX + (λ²/2)·E X²e^{|λX|}`
(`exp_le_one_add_add_sq_half_mul_exp_abs`), kills the middle term with
`hmean`, and bounds `X²e^{|λX|}` using `sq_le_exp` on the restricted range.
This ψ₁-norm sub-exponential coexists with the Lu-BDA α-form carrier in
`SubExponential/Defs.lean`: our bridge lands exactly in that structure,
discharging both of its fields (`mgf_le` and `integrable_exp_mul`).
Integrability is derived, not laundered (`e^{lx} ≤ e^{|x|/K}` on the range;
`|x|/K ≤ e^{|x|/K}`). Named-sorry fallback of this work item:
`mgf_le_of_lintegral_exp_abs_le_two`, with the norm wrapper and the
`IsSubExponential` bridge derived from it.

**Bibliographic comments.** Restricted-range MGF control of sub-exponential
variables goes back to S. N. Bernstein's 1924 inequality; the modern
two-parameter formulation is in Vershynin (HDP §2.8) and Wainwright
(*High-Dimensional Statistics*, 2019, §2.1.3).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Integrability of `exp(l·X)` on the restricted range from the ψ₁ condition
(domination `e^{lx} ≤ e^{|x|/K}` for `|l| ≤ 1/K`); discharges the
`IsSubExponential.integrable_exp_mul` field — no hypothesis laundering. -/
theorem integrable_exp_mul_of_lintegral_exp_abs_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2)
    {l : ℝ}
    -- USER-INPUT: restricted range |l| ≤ 1/K; HDP Prop 2.8.1(iv) range convention
    (hl : |l| ≤ 1 / (K : ℝ)) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by sorry

/-- First-moment integrability from the ψ₁ condition (`|x|/K ≤ e^{|x|/K}`
pointwise); makes `hmean` a claim about a genuine Bochner integral. -/
theorem integrable_of_lintegral_exp_abs_le_two {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2) :
    Integrable X μ := by sorry

/-- Raw core (HDP Prop 2.8.1 (iii)⇒(iv), `K₄ = 2K₃` book-exact): mean zero +
threshold-2 condition give the restricted-range MGF bound
`E e^{λX} ≤ exp(4λ²K²)` for `|λ| ≤ 1/(2K)`. -/
theorem mgf_le_of_lintegral_exp_abs_le_two
    -- LEAN-ONLY: probability measure; HDP §2.8 standing assumption
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Prop 2.8.1(iii)
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2)
    -- USER-INPUT: mean zero; HDP Prop 2.8.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0)
    {l : ℝ}
    -- USER-INPUT: restricted range |λ| ≤ 1/(2K); HDP Prop 2.8.1(iv)
    (hl : |l| ≤ 1 / (2 * (K : ℝ))) :
    ProbabilityTheory.mgf X μ l ≤ Real.exp (4 * l ^ 2 * (K : ℝ) ^ 2) := by sorry

/-- ψ₁-analogue of B2 (HDP Prop 2.8.1(iv)): a sub-exponential norm bound
gives the restricted-range MGF bound. -/
theorem mgf_le_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP Definition 2.8.4
    (h : subExponentialNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.8.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0)
    {l : ℝ}
    -- USER-INPUT: restricted range |λ| ≤ 1/(2K); HDP Prop 2.8.1(iv)
    (hl : |l| ≤ 1 / (2 * (K : ℝ))) :
    ProbabilityTheory.mgf X μ l ≤ Real.exp (4 * l ^ 2 * (K : ℝ) ^ 2) := by sorry

/-- Bridge into the project carrier (`α = 2√2·K` exact: `4λ²K² = λ²α²/2` and
`[−1/α, 1/α] ⊆ [−1/(2K), 1/(2K)]`); discharges both `IsSubExponential`
fields. -/
theorem isSubExponential_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.8.1
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP Definition 2.8.4
    (h : subExponentialNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.8.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    IsSubExponential X (2 * NNReal.sqrt 2 * K) μ := by sorry

end StatLean.ConcentrationInequalities
