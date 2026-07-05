import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.Orlicz.Attainment
import StatLean.ConcentrationInequalities.ForMathlib.ExpTaylorBounds

/-!
# Sub-Gaussian MGF bound from the ψ₂ norm (B2)

Mean-zero + ψ₂ condition/norm ⇒ MGF bound: if $\mathbb{E}X = 0$ and
$\|X\|_{\psi_2} \le K$ then
$$ \mathbb{E}\,e^{\lambda X} \le \exp\Bigl(\tfrac{3}{2}\,K^2\lambda^2\Bigr)
   \qquad \text{for all } \lambda \in \mathbb{R}, $$
i.e. `ProbabilityTheory.HasSubgaussianMGF X (3·K²) μ`, plus the
`IsSubGaussian` project-carrier corollary.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Proposition 2.6.1 ((iii)⇒(iv)) and Proposition
2.6.6(iv).

**Proof formalization notes.** Variance-proxy constant `C = 3` (**frozen**:
`3 * K ^ 2`; formula: book's `K₄ = √(3/2)·K₃` exactly, since Mathlib's proxy
convention `E e^{λX} ≤ e^{cλ²/2}` gives `c = 2K₄² = 3K₃²`). The proof splits
`E e^{λX} ≤ 1 + λ·EX + (λ²/2)·E X²e^{|λX|}` via the ForMathlib brick
`exp_le_one_add_add_sq_half_mul_exp_abs`, kills the middle term with `hmean`,
and bounds the remainder by the ψ₂ condition. No hypothesis laundering:
`Integrable X μ` (so `hmean` is about a genuine integral) and the
`HasSubgaussianMGF` integrability field are *derived* from the ψ₂ condition
(`|x|/K ≤ e^{(x/K)²}` resp. `e^{lx} ≤ e^{l²K²/2}·e^{(x/K)²}` pointwise) in the
two named integrability lemmas. Book Remark 2.6.2 / Exercise 2.23 ("(iv)
forces mean zero") is not formalized — scope note. Named-sorry fallback of
this work item: `integrable_exp_mul_of_lintegral_exp_sq_le_two` (domination
bookkeeping), with the MGF bound closed modulo it.

**Bibliographic comments.** The MGF characterization of sub-Gaussian
variables is due to J.-P. Kahane (1960) and Buldygin–Kozachenko (1980); the
constant-tracking equivalence proof follows HDP §2.6 (see the end-of-chapter
Notes there).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Integrability of `exp(l·X)` from the ψ₂ condition (domination
`e^{lx} ≤ e^{l²K²/2}·e^{(x/K)²}`); discharges the `HasSubgaussianMGF`
integrability field — no hypothesis laundering. -/
theorem integrable_exp_mul_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; finite dominating mass in the comparison
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    (l : ℝ) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by sorry

/-- First-moment integrability from the ψ₂ condition
(`|x|/K ≤ e^{(x/K)²}` pointwise); makes `hmean` a claim about a genuine
Bochner integral — no hypothesis laundering. -/
theorem integrable_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; finite dominating mass in the comparison
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; integrability regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    Integrable X μ := by sorry

/-- Raw core (HDP Prop 2.6.1 (iii)⇒(iv), `K₄ = √(3/2)·K₃` book-exact,
variance proxy `2K₄² = 3K²`): mean zero + threshold-2 condition give the
Mathlib sub-Gaussian MGF predicate. -/
theorem hasSubgaussianMGF_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; HDP §2.6 standing assumption
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF-predicate regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.1(iii)
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Prop 2.6.1(iii)
    (hcond : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2)
    -- USER-INPUT: mean zero; HDP Prop 2.6.1(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    ProbabilityTheory.HasSubgaussianMGF X (3 * K ^ 2) μ := by sorry

/-- **B2** (HDP Proposition 2.6.6(iv), frozen proxy `C = 3`): mean zero +
sub-Gaussian norm bound `‖X‖_{ψ₂} ≤ K` give
`HasSubgaussianMGF X (3·K²) μ`. -/
theorem hasSubgaussianMGF_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF-predicate regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.6.6(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    ProbabilityTheory.HasSubgaussianMGF X (3 * K ^ 2) μ := by sorry

/-- B2 in the project carrier: `IsSubGaussian X (3·K²) μ` (centered = raw via
`hmean` + `sub_zero` + `HasSubgaussianMGF.congr`). -/
theorem isSubGaussian_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; needed by the attainment conversion
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; MGF-predicate regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Prop 2.6.6
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Prop 2.6.6
    (h : subGaussianNorm X μ ≤ K)
    -- USER-INPUT: mean zero; HDP Prop 2.6.6(iv) hypothesis "if EX = 0"
    (hmean : ∫ x, X x ∂μ = 0) :
    IsSubGaussian X (3 * K ^ 2) μ := by sorry

end StatLean.ConcentrationInequalities
