import StatLean.CausalInference.Observational.Ignorability

/-!
# Standardization — identification of the average causal effect by outcome regression

The first identification theorem of observational causal inference. Under (mean)
ignorability and positivity, the mean potential outcome is the covariate-standardized
average of the arm regression function,

$$\mathbb E[Y(z)]=\sum_x \Pr(X=x)\,m_z(x),\qquad
  \tau=\sum_x \Pr(X=x)\,\bigl(m_1(x)-m_0(x)\bigr),$$

which is Ding's eq. (10.8) — the *g-formula* for a point treatment.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 10.1 (§10.3.1, p. 144) with its
hypotheses eqs. (10.3)–(10.4) (mean ignorability), conclusion eqs. (10.5)–(10.7), and the
discrete-covariate form eq. (10.8); Definition 10.1 (identification, p. 143); the
overlap/positivity condition of §11.2.1. (`Ding Theorem 10.1; §10.3.1; §11.2.1`.) See
also G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and
Biomedical Sciences*, Cambridge University Press, 2015, Part III. (`IR Part III`.)

**Proof formalization notes.** With a discrete covariate the proof is: decompose the
integral over covariate cells (`integral_eq_sum_cell`), replace each within-cell mean of
the potential outcome by the arm regression function
(`cellMean_true_eq_of_unconfounded`), and recombine. Positivity is what makes both arm
regression functions well defined in every cell that carries mass; on null cells both
sides contribute `0` and no hypothesis is needed. The theorem is stated under
`Unconfounded` (Ding Assumption 10.2) rather than the weaker mean-ignorability hypothesis
because the cell-mean bridge is proved from independence; a mean-ignorability version is
recorded separately as `ate_eq_sum_cellMean_of_meanIgnorable`.

**Bibliographic comments.** The formula is J. M. Robins's g-computation formula for a
point exposure, "A new approach to causal inference in mortality studies with a sustained
exposure period," *Math. Modelling* **7** (1986), 1393–1512; the standardization
terminology is standard in epidemiology.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- **Standardization identifies the treated mean** (Ding Theorem 10.1, eq. (10.5)):
`E[Y(1)] = ∑ₓ P(X = x)·m₁(x)`. -/
theorem integral_y1_eq_sum_cellMean [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrable potential outcome; Ding assumes finite means
    (hint : Integrable y1 μ) :
    ∫ ω, y1 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal * cellMean μ Z X (obs Z y1 y0) true x := by
  sorry

/-- **Standardization identifies the control mean** (Ding Theorem 10.1, eq. (10.6)). -/
theorem integral_y0_eq_sum_cellMean [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y0 μ) :
    ∫ ω, y0 ω ∂μ
      = ∑ x : 𝒳, (μ (cell X x)).toReal * cellMean μ Z X (obs Z y1 y0) false x := by
  sorry

/-- **The g-formula / standardization formula for the average causal effect**
(Ding Theorem 10.1, eqs. (10.7)–(10.8)): the average causal effect is identified by the
covariate-weighted contrast of the two arm regression functions — a functional of the
*observed-data* distribution alone. -/
theorem ate_eq_sum_cellMean_sub [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    ate μ y1 y0
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * (cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x) := by
  sorry

/-- **The average causal effect is the average conditional effect** (Ding §10.3.1):
`τ = ∑ₓ P(X = x)·τ(x)`. No identification assumption is involved — this is the law of
total expectation. -/
theorem ate_eq_sum_cate [IsProbabilityMeasure μ]
    (hX : Measurable X)
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ) :
    ate μ y1 y0 = ∑ x : 𝒳, (μ (cell X x)).toReal * cate μ X y1 y0 x := by
  sorry

/-- **Cell-wise identification** (Ding Theorem 10.1): the conditional average causal effect
is the contrast of the arm regression functions in that cell. -/
theorem cate_eq_cellMean_sub [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0) :
    cate μ X y1 y0 x
      = cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x := by
  sorry

/-- **Standardization under mean ignorability** (Ding Theorem 10.1 with its stated
hypotheses (10.3)–(10.4)): the identification formula needs only equality of the arm
conditional means, not full independence. -/
theorem ate_eq_sum_cellMean_of_meanIgnorable [IsProbabilityMeasure μ]
    -- USER-INPUT: mean ignorability for both potential outcomes; Ding eqs. (10.3)–(10.4)
    (hm1 : MeanIgnorable μ Z y1 X) (hm0 : MeanIgnorable μ Z y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    ate μ y1 y0
      = ∑ x : 𝒳, (μ (cell X x)).toReal
          * (cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x) := by
  sorry

end StatLean.CausalInference
