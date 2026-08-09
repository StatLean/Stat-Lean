import StatLean.CausalInference.Observational.Standardization

/-!
# Inverse-probability weighting — identification by reweighting the observed arms

Weighting each treated unit by `1/e(X)` and each control unit by `1/(1-e(X))` recreates
the population that would have been observed had everyone been treated (resp. untreated):

$$\mathbb E[Y(1)]=\mathbb E\Bigl[\frac{ZY}{e(X)}\Bigr],\qquad
  \mathbb E[Y(0)]=\mathbb E\Bigl[\frac{(1-Z)Y}{1-e(X)}\Bigr],\qquad
  \tau=\mathbb E\Bigl[\frac{ZY}{e(X)}-\frac{(1-Z)Y}{1-e(X)}\Bigr].$$

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 11.2 (§11.2.1, p. 158), whose hypotheses
are strong ignorability `Z ⫫ {Y(1),Y(0)} | X` (Assumption 10.2) **and** overlap
`0 < e(X) < 1`; §11.2.2 (p. 160) for the Horvitz–Thompson and Hájek forms.
(`Ding Theorem 11.2; §11.2.2`.) See also G. W. Imbens and D. B. Rubin, *Causal Inference
for Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015,
ch. 12. (`IR ch. 12`.)

**Proof formalization notes.** The route is cell-wise: decompose over covariate cells,
and inside a cell the weighted integrand is `1{Z=1}·Y/e(x)`, whose mean is
`e(x)·m₁(x)/e(x) = m₁(x)` — the weight exactly cancels the arm probability. Summing
against the cell probabilities and applying `Standardization.integral_y1_eq_sum_cellMean`
gives `E[Y(1)]`. Overlap is what makes the division legitimate on every cell that carries
mass; on null cells both sides vanish.

**Bibliographic comments.** D. G. Horvitz and D. J. Thompson, "A generalization of
sampling without replacement from a finite universe," *J. Amer. Statist. Assoc.* **47**
(1952), 663–685; the causal-inference use is due to J. M. Robins and collaborators.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- Inside a covariate cell, the inverse-probability-weighted treated outcome has mean
equal to the treated arm regression function: the weight `1/e(x)` cancels the probability
of being treated. -/
theorem integral_cond_cell_ipw_treated [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrability of the observed outcome
    (hint : Integrable (obs Z y1 y0) μ) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) > 0`; Ding §11.2.1
    (hpos : 0 < propensity μ Z X x) :
    ∫ ω, ind (Z ω) * obs Z y1 y0 ω / propensity μ Z X x ∂(μ[|cell X x])
      = cellMean μ Z X (obs Z y1 y0) true x := by
  sorry

/-- Inside a covariate cell, the inverse-probability-weighted control outcome has mean
equal to the control arm regression function. -/
theorem integral_cond_cell_ipw_control [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) (hint : Integrable (obs Z y1 y0) μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) < 1`; Ding §11.2.1
    (hpos : propensity μ Z X x < 1) :
    ∫ ω, (1 - ind (Z ω)) * obs Z y1 y0 ω / (1 - propensity μ Z X x) ∂(μ[|cell X x])
      = cellMean μ Z X (obs Z y1 y0) false x := by
  sorry

/-- **IPW identifies the treated mean** (Ding Theorem 11.2): `E[Y(1)] = E[ZY/e(X)]`. -/
theorem ipwTreated_eq_integral_y1 [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrable potential outcome; Ding assumes finite means
    (hi1 : Integrable y1 μ) :
    ipwTreated μ Z X (obs Z y1 y0) = ∫ ω, y1 ω ∂μ := by
  sorry

/-- **IPW identifies the control mean** (Ding Theorem 11.2):
`E[Y(0)] = E[(1-Z)Y/(1-e(X))]`. -/
theorem ipwControl_eq_integral_y0 [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi0 : Integrable y0 μ) :
    ipwControl μ Z X (obs Z y1 y0) = ∫ ω, y0 ω ∂μ := by
  sorry

/-- **IPW identifies the average causal effect** (Ding Theorem 11.2): the headline
weighting formula. -/
theorem ipwATE_eq_ate [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    ipwATE μ Z X (obs Z y1 y0) = ate μ y1 y0 := by
  sorry

/-- **Bounded weights under strong overlap** (Ding §11.2.3): if the propensity score stays
in `[α, 1-α]`, the treated inverse-probability weight is at most `1/α`. This is the
quantitative statement behind the practical warning that weak overlap inflates variance. -/
theorem ind_div_propensity_le [IsProbabilityMeasure μ] {α : ℝ}
    -- USER-INPUT: strong overlap `α ≤ e(X) ≤ 1 - α`; Ding §11.2.3
    (hα : 0 < α) (hover : StronglyOverlapping μ Z X α) {ω : Ω}
    -- USER-INPUT: the unit's covariate cell carries mass
    (hcell : μ (cell X (X ω)) ≠ 0) :
    ind (Z ω) / propensity μ Z X (X ω) ≤ 1 / α := by
  sorry

end StatLean.CausalInference
