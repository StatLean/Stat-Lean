import StatLean.CausalInference.Observational.IPW

/-!
# Augmented inverse-probability weighting — the doubly robust identity

The augmented functional combines an outcome model `m̄₁` with a propensity model `ē`,

$$\tilde\mu_1^{\mathrm{dr}}
  =\mathbb E\Bigl[\bar m_1(X)+\frac{Z\{Y-\bar m_1(X)\}}{\bar e(X)}\Bigr],$$

and is **doubly robust**: it equals `E[Y(1)]` if *either* model is correct, neither needs
to be. The mechanism is the exact product-bias identity

$$\tilde\mu_1^{\mathrm{dr}}-\mathbb E[Y(1)]
  =\mathbb E\Bigl[\frac{e(X)-\bar e(X)}{\bar e(X)}\bigl\{m_1(X)-\bar m_1(X)\bigr\}\Bigr],$$

whose right-hand side is a *product* of the two model errors, so it vanishes as soon as
one factor does.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 12.1 (§12.1.1, p. 170), under
ignorability `Z ⫫ {Y(1),Y(0)} | X` and overlap `0 < e(X) < 1`, with the functionals of
eqs. (12.3)–(12.6); the product-bias identity appears inside the proof of Theorem 12.1
(p. 171) and again in §12.4 (p. 177) — it carries no number of its own.
(`Ding Theorem 12.1; §12.1, §12.4`.)

**Scope.** This is the *algebraic* double-robustness of the population functional, which
is what Ding's ch. 12 establishes. Estimation theory for the sample version (asymptotic
normality, efficiency, cross-fitting) is deliberately out of scope — it needs
semiparametric machinery beyond the two reference texts.

**Proof formalization notes.** Everything is a cell-wise computation. In cell `x` the
augmented integrand has mean
`m̄₁(x) + e(x)·(m₁(x) - m̄₁(x))/ē(x)`, and subtracting `m₁(x)` gives
`(e(x) - ē(x))·(m₁(x) - m̄₁(x))/ē(x)` after collecting terms; summing against the cell
probabilities is the identity. The two robustness corollaries then just observe that one
factor is `0`. Note that the working propensity must be bounded away from `0` on cells
that carry mass — otherwise the functional itself is undefined — which is a hypothesis on
the *working* model, separate from the true overlap condition.

**Bibliographic comments.** J. M. Robins, A. Rotnitzky and L. P. Zhao, "Estimation of
regression coefficients when some regressors are not always observed," *J. Amer. Statist.
Assoc.* **89** (1994), 846–866; the double-robustness terminology is from
J. M. Robins, "Robust estimation in sequentially ignorable missing data and causal
inference models," *Proc. Amer. Statist. Assoc.* (2000), 6–10.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}
  {ebar m1bar m0bar : 𝒳 → ℝ}

/-- The cell-wise mean of the augmented integrand for the treated arm. -/
theorem integral_cond_cell_aipwTreated [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) (hint : Integrable (obs Z y1 y0) μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: the working propensity is nonzero on this cell, else the functional is
    -- undefined; Ding §12.1 (working model, not the truth)
    (hebar : ebar x ≠ 0) :
    ∫ ω, (m1bar (X ω) + ind (Z ω) * (obs Z y1 y0 ω - m1bar (X ω)) / ebar (X ω))
        ∂(μ[|cell X x])
      = m1bar x
        + propensity μ Z X x * (cellMean μ Z X (obs Z y1 y0) true x - m1bar x) / ebar x := by
  sorry

/-- **The product-bias identity for the treated functional** (Ding, proof of Theorem 12.1,
p. 171; §12.4): the error of the augmented functional is the covariate average of the
*product* of the propensity-model error and the outcome-model error. -/
theorem aipwTreated_sub_integral_y1_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap for the true propensity; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ)
    -- USER-INPUT: the working propensity never vanishes; Ding §12.1
    (hebar : ∀ x, ebar x ≠ 0) :
    aipwTreated μ Z X (obs Z y1 y0) ebar m1bar - ∫ ω, y1 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * ((propensity μ Z X x - ebar x) / ebar x
              * (cellMean μ Z X (obs Z y1 y0) true x - m1bar x)) := by
  sorry

/-- **Double robustness of the treated functional, correct propensity branch**
(Ding Theorem 12.1(1)): if the working propensity is the truth, the augmented functional
identifies `E[Y(1)]` whatever the outcome model. -/
theorem aipwTreated_eq_of_correct_propensity [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hebar : ∀ x, ebar x ≠ 0)
    -- USER-INPUT: the propensity model is correctly specified; Ding Theorem 12.1
    (hcorrect : ∀ x, ebar x = propensity μ Z X x) :
    aipwTreated μ Z X (obs Z y1 y0) ebar m1bar = ∫ ω, y1 ω ∂μ := by
  sorry

/-- **Double robustness of the treated functional, correct outcome branch**
(Ding Theorem 12.1(1)): if the working outcome model is the truth, the augmented
functional identifies `E[Y(1)]` whatever the propensity model. -/
theorem aipwTreated_eq_of_correct_outcome [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hebar : ∀ x, ebar x ≠ 0)
    -- USER-INPUT: the outcome model is correctly specified; Ding Theorem 12.1
    (hcorrect : ∀ x, μ (cell X x) ≠ 0 → m1bar x = cellMean μ Z X (obs Z y1 y0) true x) :
    aipwTreated μ Z X (obs Z y1 y0) ebar m1bar = ∫ ω, y1 ω ∂μ := by
  sorry

/-- **Product-bias identity for the control functional** (Ding §12.4). -/
theorem aipwControl_sub_integral_y0_eq [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi0 : Integrable y0 μ)
    -- USER-INPUT: the working propensity is never one; Ding §12.1
    (hebar : ∀ x, 1 - ebar x ≠ 0) :
    aipwControl μ Z X (obs Z y1 y0) ebar m0bar - ∫ ω, y0 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * ((ebar x - propensity μ Z X x) / (1 - ebar x)
              * (cellMean μ Z X (obs Z y1 y0) false x - m0bar x)) := by
  sorry

/-- **The doubly robust identification theorem** (Ding Theorem 12.1(3)): if the propensity
model is correct, the augmented functional identifies the average causal effect —
regardless of the outcome models. -/
theorem aipwATE_eq_ate_of_correct_propensity [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: the propensity model is correctly specified; Ding Theorem 12.1
    (hcorrect : ∀ x, ebar x = propensity μ Z X x)
    -- USER-INPUT: the (true) propensity is never `0` or `1`, so the weights are defined
    (he0 : ∀ x, ebar x ≠ 0) (he1 : ∀ x, 1 - ebar x ≠ 0) :
    aipwATE μ Z X (obs Z y1 y0) ebar m1bar m0bar = ate μ y1 y0 := by
  sorry

/-- **The doubly robust identification theorem, outcome branch** (Ding Theorem 12.1(3)):
if *both* outcome models are correct, the augmented functional identifies the average
causal effect — regardless of the propensity model. -/
theorem aipwATE_eq_ate_of_correct_outcome [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both outcome models are correctly specified; Ding Theorem 12.1
    (hc1 : ∀ x, μ (cell X x) ≠ 0 → m1bar x = cellMean μ Z X (obs Z y1 y0) true x)
    (hc0 : ∀ x, μ (cell X x) ≠ 0 → m0bar x = cellMean μ Z X (obs Z y1 y0) false x)
    -- USER-INPUT: the working weights are defined
    (he0 : ∀ x, ebar x ≠ 0) (he1 : ∀ x, 1 - ebar x ≠ 0) :
    aipwATE μ Z X (obs Z y1 y0) ebar m1bar m0bar = ate μ y1 y0 := by
  sorry

end StatLean.CausalInference
