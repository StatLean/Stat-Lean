import StatLean.ConcentrationInequalities.Orlicz.Basic
import StatLean.ConcentrationInequalities.Orlicz.Generators

/-!
# Orlicz norm — attainment, definiteness, and the book-form conversions

Limiting behavior of the Luxemburg infimum. The **attainment lemma** is the
book's silent WLOG "if $\|X\|_{\psi_2} \le K$ then $\mathbb{E}\exp(X^2/K^2)
\le 2$": the defining condition holds *at* any upper bound of the norm, not
just strictly above it. **Definiteness** is
$$ \|X\|_\psi = 0 \iff X = 0 \text{ a.e.} $$
The four ψ₂/ψ₁ conversion lemmas translate `subGaussianNorm X μ ≤ K` into the
book-form threshold-2 conditions $\mathbb{E}\exp(X^2/K^2) \le 2$ (resp.
$\mathbb{E}\exp(|X|/K) \le 2$) and back; every bridge (B1–B3 and the ψ₁
analogues) consumes them.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press: Definition 2.6.4 / Eq. (2.18) and Definition
2.8.4 / Eq. (2.25) (the norms), Exercise 2.42 (definiteness), and the silent
normalization step in the proofs of Propositions 2.6.6, 2.8.1 and Lemmas
2.8.5–2.8.6.

**Proof formalization notes.** Mathlib has no packaged Luxemburg-attainment
lemma. The attainment proof runs monotone convergence
(`MeasureTheory.lintegral_iSup_directed`) along `Kₙ = K·(1 + 1/(n+1)) ↓ K`,
each `Kₙ` in the gauge set by upward closure; it needs `MonotoneOn ψ (Ici 0)`
**and** `Continuous ψ` together (a merely left-continuous ψ would break the
sup-identification silently). The ±1 shift between the threshold-1 Luxemburg
condition on `ψ = exp − 1` and the threshold-2 book condition on `exp` is done
*additively* (`ofReal (e^u − 1) + 1 = ofReal (e^u)` pointwise, then
`lintegral_add_right'`) to avoid `ENNReal` truncated subtraction; the
conversions therefore need `[IsProbabilityMeasure μ]` (`∫⁻ 1 ∂μ = μ univ`).
Named-sorry fallback of this work item: `orliczNorm_eq_zero_iff` (the
least-consumed declaration; the attainment lemma and the four conversions
must close since every bridge consumes them).

**Bibliographic comments.** Attainment of the Luxemburg gauge under
continuity is classical Orlicz-space theory (Luxemburg 1955; see also
Rao–Ren, *Theory of Orlicz Spaces*, Dekker 1991, §III); the threshold-2
formulation is Vershynin's (HDP §2.6/§2.8 Notes).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Attainment** (the book's silent WLOG `‖X‖_{ψ₂} ≤ K ⇒ E exp(X²/K²) ≤ 2`):
the Luxemburg condition holds at any upper bound `K` of the norm. Monotone
convergence along `Kₙ ↓ K` via `lintegral_iSup_directed`. -/
theorem lintegral_le_one_of_orliczNorm_le {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- LEAN-ONLY: continuity of ψ; needed for the sup-identification along Kₙ ↓ K,
    -- satisfied by both generators (Generators.lean), no book scope change
    (hψ_cont : Continuous ψ)
    {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Mathlib-side regularity for lintegral limits
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP §2.6.1 (the norm bound is at a scale K > 0)
    (hK : 0 < K)
    -- USER-INPUT: norm bound ‖X‖_ψ ≤ K; HDP Prop 2.6.6 / 2.8.1 proofs (WLOG step)
    (h : orliczNorm ψ X μ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ ≤ 1 := by sorry

/-- **Definiteness** (HDP Exercise 2.42): the Orlicz norm vanishes iff
`X = 0` a.e.; forward direction via Markov at each ε and `K ↓ 0`. -/
theorem orliczNorm_eq_zero_iff {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- USER-INPUT: ψ(0) ≤ 0 (book: ψ(0) = 0); HDP Exercise 2.42 (Orlicz function)
    (hψ0 : ψ 0 ≤ 0)
    -- USER-INPUT: ψ → ∞ at ∞; HDP Exercise 2.42 (Orlicz function, definiteness)
    (hψ_top : Filter.Tendsto ψ Filter.atTop Filter.atTop)
    {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-argument regularity, no book scope
    (hX : AEMeasurable X μ) :
    orliczNorm ψ X μ = 0 ↔ X =ᵐ[μ] 0 := by sorry

/-- `‖X‖_{ψ₂} ≤ K` unfolded to the book form `E exp(X²/K²) ≤ 2`
(HDP Definition 2.6.4). -/
theorem lintegral_exp_sq_le_two_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; attainment-lemma regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.6.4
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Definition 2.6.4
    (h : subGaussianNorm X μ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2 := by sorry

/-- Reverse conversion: the book form `E exp(X²/K²) ≤ 2` bounds the norm by
`K` (HDP Definition 2.6.4; additive −1 shift, no `ENNReal` tsub). -/
theorem subGaussianNorm_le_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.6.4
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Definition 2.6.4
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    subGaussianNorm X μ ≤ (K : ℝ≥0∞) := by sorry

/-- `‖X‖_{ψ₁} ≤ K` unfolded to the book form `E exp(|X|/K) ≤ 2`
(HDP Definition 2.8.4). -/
theorem lintegral_exp_abs_le_two_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; attainment-lemma regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.8.4
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP Definition 2.8.4
    (h : subExponentialNorm X μ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2 := by sorry

/-- Reverse conversion: the book form `E exp(|X|/K) ≤ 2` bounds the norm by
`K` (HDP Definition 2.8.4). -/
theorem subExponentialNorm_le_of_lintegral_exp_abs_le_two
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.8.4
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Definition 2.8.4
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2) :
    subExponentialNorm X μ ≤ (K : ℝ≥0∞) := by sorry

end StatLean.ConcentrationInequalities
