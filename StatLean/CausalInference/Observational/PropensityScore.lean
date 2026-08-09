import StatLean.CausalInference.Observational.Ignorability

/-!
# The propensity score — balancing and dimension reduction

The propensity score `e(x) = P(Z = 1 | X = x)` is a **balancing score**: conditioning on it
alone makes the treatment probability constant across covariate values,

$$\Pr(Z=1\mid X=x)=\Pr\bigl(Z=1\mid e(X)=e(x)\bigr),$$

and under ignorability it suffices to adjust for `e(X)` instead of the full covariate —
the dimension-reduction property that makes propensity-score methods practical. This file
also proves the weighted-balance identity `E[Z h(X)/e(X)] = E[(1-Z) h(X)/(1-e(X))]` that
underlies weighting diagnostics.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 11.1 (the propensity score, p. 153);
Theorem 11.3 (§11.3.1, p. 163: `Z ⫫ X | e(X)`, which needs *no* ignorability assumption,
together with the weighted balance eq. (11.2)); Theorem 11.1 (§11.1.1, p. 154: strong
ignorability given `X` implies strong ignorability given `e(X)`); §11.2.1 for
overlap. (`Ding Definition 11.1; Theorems 11.1, 11.3`.) Propensity-score design in
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, chs. 12–13. (`IR chs. 12–13`.)

**Scope.** Ding's Theorem 11.1 is stated as a conditional *independence*
`{Y(1),Y(0)} ⫫ Z | e(X)`. What is formalized here is its **mean form**
(`integral_cond_propensityLevel_arm_eq`): within a level set of the propensity score, the
arm-conditional mean of a potential outcome equals its unconditional mean. That is the
form every downstream identification result consumes, and it avoids building a
conditional-independence-given-a-real-valued-statistic layer that StatLean does not have.

**Proof formalization notes.** `propensityLevel μ Z X v` is the preimage `{e(X) = v}`, a
finite union of covariate cells because `𝒳` is finite. Both balancing results reduce to:
each cell in the level set has treatment probability exactly `v`, so the mixture over
cells also has treatment probability `v`. The weighted-balance identity is a cell-wise
computation in which the factor `e(x)` cancels.

**Bibliographic comments.** P. R. Rosenbaum and D. B. Rubin, "The central role of the
propensity score in observational studies for causal effects," *Biometrika* **70** (1983),
41–55 (Theorems 1–3 there are the balancing and dimension-reduction properties).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- The **level set of the propensity score**: the units whose covariate cell has
propensity `v`. A finite union of covariate cells. -/
def propensityLevel (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (v : ℝ) : Set Ω :=
  {ω | propensity μ Z X (X ω) = v}

/-- The propensity score of a cell is its conditional treatment probability — the
definition, restated for use. -/
theorem propensity_eq_cond (x : 𝒳) :
    propensity μ Z X x = ((μ[|cell X x]) (treatedEvent Z)).toReal := rfl

/-- The propensity score lies in `[0, 1]`. -/
theorem propensity_mem_Icc [IsProbabilityMeasure μ] (x : 𝒳) :
    propensity μ Z X x ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- **The propensity score is a balancing score** (Ding Theorem 11.3): the conditional
treatment probability given the whole covariate equals the conditional treatment
probability given only the propensity score. No ignorability assumption is used. -/
theorem cond_treated_propensityLevel_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hZ : Measurable Z) (hX : Measurable X) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0) :
    ((μ[|propensityLevel μ Z X (propensity μ Z X x)]) (treatedEvent Z)).toReal
      = propensity μ Z X x := by
  sorry

/-- **`Z ⫫ X | e(X)`, mean form** (Ding Theorem 11.3): within a level set of the
propensity score, the treatment probability is the same in every covariate cell, so the
covariate carries no further information about the treatment. -/
theorem cond_treated_eq_of_propensity_eq [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) {x x' : 𝒳}
    (hcell : μ (cell X x) ≠ 0) (hcell' : μ (cell X x') ≠ 0)
    -- USER-INPUT: the two cells share a propensity value; Ding Theorem 11.3
    (hprop : propensity μ Z X x = propensity μ Z X x') :
    ((μ[|cell X x]) (treatedEvent Z)).toReal = ((μ[|cell X x']) (treatedEvent Z)).toReal := by
  sorry

/-- **Weighted covariate balance** (Ding eq. (11.2)): for any function of the covariate,
inverse-probability weighting equalizes the two arms. This is the population identity
behind balance diagnostics. -/
theorem integral_ind_div_propensity_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: overlap `0 < e(X) < 1`; Ding §11.2.1 (the weights must be finite)
    (hpos : Positive μ Z X)
    (hZ : Measurable Z) (hX : Measurable X) (h : 𝒳 → ℝ) :
    ∫ ω, ind (Z ω) * h (X ω) / propensity μ Z X (X ω) ∂μ
      = ∫ ω, (1 - ind (Z ω)) * h (X ω) / (1 - propensity μ Z X (X ω)) ∂μ := by
  sorry

/-- **The inverse-probability weights have mean one** (Ding §11.2.2): `E[Z/e(X)] = 1`.
The special case `h ≡ 1` of the balance identity, and the reason the Hájek estimator's
denominator is consistent for one. -/
theorem integral_ind_div_propensity_eq_one [IsProbabilityMeasure μ]
    (hpos : Positive μ Z X) (hZ : Measurable Z) (hX : Measurable X) :
    ∫ ω, ind (Z ω) / propensity μ Z X (X ω) ∂μ = 1 := by
  sorry

/-- **Dimension reduction, mean form** (Ding Theorem 11.1): under strong ignorability
given the covariate, the arm-conditional mean of a potential outcome within a level set of
the propensity score equals its unconditional mean there — adjusting for the scalar
`e(X)` is as good as adjusting for `X`. -/
theorem integral_cond_propensityLevel_arm_eq [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability given `X`; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y1 μ) {v : ℝ}
    -- USER-INPUT: a propensity level of positive probability
    (hlevel : μ (propensityLevel μ Z X v) ≠ 0)
    -- USER-INPUT: the level is a genuine treatment probability; Ding §11.2.1
    (hv : 0 < v) :
    ∫ ω, y1 ω ∂(μ[|treatedEvent Z ∩ propensityLevel μ Z X v])
      = ∫ ω, y1 ω ∂(μ[|propensityLevel μ Z X v]) := by
  sorry

end StatLean.CausalInference
