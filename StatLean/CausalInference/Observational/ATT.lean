import StatLean.CausalInference.Observational.IPW

/-!
# The effect on the treated, and weighted average treatment effects

Identification of `τ_T = E[Y(1) - Y(0) | Z = 1]` needs *less* than identification of `τ`:
only the control potential outcome must be ignorable, and only one-sided overlap
`e(X) < 1` is required, since the treated arm's own outcomes are observed. Two formulas
are proved — outcome regression and weighting — and then the general family of
`h`-weighted estimands that contains `τ`, `τ_T`, `τ_C` and the overlap-weighted effect
`τ_O` as special cases.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Assumption 13.1 (p. 181: `Z ⫫ Y(0) | X` and
`e(X) < 1`); Theorem 13.1 (p. 181, eq. (13.1): the outcome-regression form); Theorem 13.2
(§13.2, p. 183, eqs. (13.2)–(13.3): the weighting form with the odds weight
`e(X)/{1-e(X)}`); Theorem 13.4 (§13.4, p. 188: the `h`-weighted estimands, with the table
`h = 1 ↦ τ`, `h = e ↦ τ_T`, `h = 1-e ↦ τ_C`, `h = e(1-e) ↦ τ_O`).
(`Ding Assumption 13.1; Theorems 13.1, 13.2, 13.4`.) Compare G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, ch. 12. (`IR ch. 12`.)

**Proof formalization notes.** `Assumption131` bundles Ding's one-sided ignorability with
one-sided overlap; it is *weaker* than `Unconfounded ∧ Positive`, and the implication is
recorded (`Assumption131.of_unconfounded`). The proofs are the cell-wise computations of
`IPW`/`Standardization` restricted to the treated arm, using
`P(X = x | Z = 1) = P(X = x)·e(x)/e` (Bayes in a cell, `cond_cell_given_treated`). The
weighted-estimand theorem is stated with the normalizing denominator `E[h(X)]` explicit,
so no positivity of `E[h]` is needed for the statement; the four special cases carry the
hypotheses that make their denominators nonzero.

**Bibliographic comments.** The overlap weight `h = e(1-e)` and its optimality properties
are from F. Li, K. L. Morgan and A. M. Zaslavsky, "Balancing covariates via propensity
score weighting," *J. Amer. Statist. Assoc.* **113** (2018), 390–400.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- **Ding's Assumption 13.1**: ignorability of the *control* potential outcome given the
covariate, together with one-sided overlap `e(X) < 1`. Everything needed to identify the
effect on the treated. -/
structure Assumption131 (μ : Measure Ω) (Z : Ω → Bool) (y0 : Ω → ℝ) (X : Ω → 𝒳) : Prop where
  /-- Constitutive (Ding Assumption 13.1): the control potential outcome is ignorable. -/
  ignorable : Ignorable μ Z y0 X
  /-- Constitutive (Ding Assumption 13.1): one-sided overlap — every covariate cell that
  carries mass contains control units. -/
  overlap : ∀ x : 𝒳, μ (cell X x) ≠ 0 → propensity μ Z X x < 1

/-- Strong ignorability plus two-sided overlap implies Ding's Assumption 13.1. -/
theorem Assumption131.of_unconfounded (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    -- USER-INPUT: measurability of the potential outcomes; needed to project the pair
    (hy1 : Measurable y1) (hy0 : Measurable y0) :
    Assumption131 μ Z y0 X := by
  sorry

/-- **Bayes in a covariate cell**: the covariate distribution among the treated reweights
the marginal by the propensity odds, `P(X = x | Z = 1) = P(X = x)·e(x)/e`. -/
theorem cond_cell_given_treated [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) (x : 𝒳)
    -- USER-INPUT: some unit is treated; else conditioning on `{Z = 1}` is vacuous
    (hT : μ (treatedEvent Z) ≠ 0) :
    ((μ[|treatedEvent Z]) (cell X x)).toReal
      = (μ (cell X x)).toReal * propensity μ Z X x / (μ (treatedEvent Z)).toReal := by
  sorry

/-- **Outcome-regression identification of the effect on the treated**
(Ding Theorem 13.1, eq. (13.1)): the counterfactual mean for the treated is the treated
units' average of the *control* regression function. -/
theorem att_eq_sub_sum_cellMean [IsProbabilityMeasure μ]
    -- USER-INPUT: Ding Assumption 13.1
    (h131 : Assumption131 μ Z y0 X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: some unit is treated; Ding ch. 13
    (hT : μ (treatedEvent Z) ≠ 0) :
    att μ Z y1 y0
      = ∫ ω, obs Z y1 y0 ω ∂(μ[|treatedEvent Z])
        - ∑ x : 𝒳, ((μ[|treatedEvent Z]) (cell X x)).toReal
            * cellMean μ Z X (obs Z y1 y0) false x := by
  sorry

/-- **Weighting identification of the effect on the treated** (Ding Theorem 13.2,
eqs. (13.2)–(13.3)): the counterfactual mean for the treated is an odds-weighted average
over the *control* units, `E[(e(X)/e)·((1-Z)/(1-e(X)))·Y]`. -/
theorem att_eq_sub_integral_odds_weight [IsProbabilityMeasure μ]
    (h131 : Assumption131 μ Z y0 X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) (hT : μ (treatedEvent Z) ≠ 0) :
    att μ Z y1 y0
      = ∫ ω, obs Z y1 y0 ω ∂(μ[|treatedEvent Z])
        - ∫ ω, (propensity μ Z X (X ω) / (μ (treatedEvent Z)).toReal)
              * ((1 - ind (Z ω)) / (1 - propensity μ Z X (X ω))) * obs Z y1 y0 ω ∂μ := by
  sorry

/-- The **`h`-weighted average treatment effect** (Ding Theorem 13.4, §13.4): the family of
estimands obtained by tilting the covariate distribution by `h`. -/
noncomputable def weightedATE (μ : Measure Ω) (X : Ω → 𝒳) (y1 y0 : Ω → ℝ) (h : 𝒳 → ℝ) : ℝ :=
  (∫ ω, h (X ω) * (y1 ω - y0 ω) ∂μ) / ∫ ω, h (X ω) ∂μ

/-- **Identification of the weighted estimands** (Ding Theorem 13.4): under ignorability
and overlap, every `h`-weighted effect is identified by weighting the observed data. -/
theorem weightedATE_eq_ipw [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) (h : 𝒳 → ℝ) :
    weightedATE μ X y1 y0 h
      = (∫ ω, (ind (Z ω) * h (X ω) * obs Z y1 y0 ω / propensity μ Z X (X ω)
              - (1 - ind (Z ω)) * h (X ω) * obs Z y1 y0 ω / (1 - propensity μ Z X (X ω))) ∂μ)
          / ∫ ω, h (X ω) ∂μ := by
  sorry

/-- **The weight `h ≡ 1` gives the average causal effect** (Ding Theorem 13.4, first table
row). -/
theorem weightedATE_one [IsProbabilityMeasure μ]
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ) :
    weightedATE μ X y1 y0 (fun _ => 1) = ate μ y1 y0 := by
  sorry

/-- **The weight `h = e` gives the effect on the treated** (Ding Theorem 13.4, second table
row): tilting the covariate distribution by the propensity score reproduces the treated
population. -/
theorem weightedATE_propensity [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    -- USER-INPUT: some unit is treated; Ding ch. 13
    (hT : μ (treatedEvent Z) ≠ 0) :
    weightedATE μ X y1 y0 (propensity μ Z X) = att μ Z y1 y0 := by
  sorry

/-- **The weight `h = 1 - e` gives the effect on the controls** (Ding Theorem 13.4, third
table row). -/
theorem weightedATE_one_sub_propensity [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    -- USER-INPUT: some unit is untreated; Ding ch. 13
    (hC : μ {ω | Z ω = false} ≠ 0) :
    weightedATE μ X y1 y0 (fun x => 1 - propensity μ Z X x) = atc μ Z y1 y0 := by
  sorry

end StatLean.CausalInference
