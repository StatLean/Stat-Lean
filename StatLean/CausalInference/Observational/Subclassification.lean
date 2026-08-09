import StatLean.CausalInference.Observational.Standardization

/-!
# Subclassification — stratifying on the covariate or on the propensity score

Standardization, read as an estimator: split the sample into subclasses, take the
difference in means inside each, and average the results with subclass weights,

$$\hat\tau_{\mathrm{sub}}=\sum_k \hat\pi_{[k]}\bigl(\bar Y_{1[k]}-\bar Y_{0[k]}\bigr).$$

This file records the population identity behind that recipe — it is exactly the
standardization formula — and the propensity-score version: because the propensity score is
a balancing score, stratifying on it identifies the average causal effect just as
stratifying on the full covariate does.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §10.4.1 (p. 146: "stratification or
standardization based on discrete covariates", where the estimator
`τ̂ = ∑_k π_[k]{Ŷ_[k](1) - Ŷ_[k](0)}` is introduced and noted to be *identical* to the
stratified/post-stratified estimator of ch. 5 — stated in the text, no theorem number),
with identification by **Theorem 10.1** and its discrete form eq. (10.8); §11.1.2
(pp. 155–158: propensity-score stratification, licensed by **Theorem 11.1**, again with no
separate numbered theorem). (`Ding §10.4.1; Theorem 10.1; §11.1.2; Theorem 11.1`.)
Subclassification on the propensity score is ch. 17 of G. W. Imbens and D. B. Rubin,
*Causal Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University
Press, 2015. (`IR ch. 17`.)

**Proof formalization notes.** `subclassEstimand` is written with a general subclass map
`s : 𝒳 → 𝒦` so that both cases are instances: `s = id` gives covariate stratification and
`s = ` (a discretization of) `e(·)` gives propensity stratification. The covariate version
is a regrouping of `Standardization.ate_eq_sum_cellMean_sub` — a finite `Finset.sum_fiberwise`
— and the propensity version additionally needs that the arm regression functions are
constant on a propensity level set, which is where `PropensityScore` is used. Subclasses of
probability zero contribute `0` on both sides and need no hypothesis.

**Bibliographic comments.** Subclassification is W. G. Cochran, "The effectiveness of
adjustment by subclassification in removing bias in observational studies," *Biometrics*
**24** (1968), 295–313; the propensity-score version is Rosenbaum–Rubin (1983).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {𝒦 : Type*} [Fintype 𝒦] [DecidableEq 𝒦]
  {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- The **subclass** `{s(X) = k}` induced by a subclass map `s`. -/
def subclass (X : Ω → 𝒳) (s : 𝒳 → 𝒦) (k : 𝒦) : Set Ω := (s ∘ X) ⁻¹' {k}

/-- The **subclassification estimand**: the subclass-probability-weighted average of the
within-subclass arm contrasts (Ding §10.4.1). -/
noncomputable def subclassEstimand (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (s : 𝒳 → 𝒦) : ℝ :=
  ∑ k : 𝒦, (μ (subclass X s k)).toReal
    * (∫ ω, Y ω ∂(μ[|{ω | Z ω = true} ∩ subclass X s k])
        - ∫ ω, Y ω ∂(μ[|{ω | Z ω = false} ∩ subclass X s k]))

/-- The probability of a subclass is the sum of the probabilities of the covariate cells it
contains. -/
theorem measure_subclass_eq_sum [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    -- USER-INPUT: measurability of the covariate; user-supplied data
    (hX : Measurable X) (s : 𝒳 → 𝒦) (k : 𝒦) :
    (μ (subclass X s k)).toReal
      = ∑ x ∈ Finset.univ.filter fun x => s x = k, (μ (cell X x)).toReal := by
  sorry

/-- **Exact subclassification on the covariate identifies the average causal effect**
(Ding §10.4.1, from Theorem 10.1): taking each covariate value as its own subclass, the
subclassification estimand is the average causal effect. -/
theorem subclassEstimand_id_eq_ate [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) :
    subclassEstimand μ Z X (obs Z y1 y0) (id : 𝒳 → 𝒳) = ate μ y1 y0 := by
  sorry

/-- **Subclassification is standardization**: for any subclass map the estimand regroups
the covariate cells, so a coarser subclassification is the cell-weighted average of the
coarser arm contrasts (Ding §10.4.1, "identical to the stratified estimator"). -/
theorem subclassEstimand_eq_sum_fiber [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    (hZ : Measurable Z) (hX : Measurable X) (s : 𝒳 → 𝒦) (Y : Ω → ℝ)
    -- USER-INPUT: integrability of the observed outcome
    (hint : Integrable Y μ) :
    subclassEstimand μ Z X Y s
      = ∑ k : 𝒦, (μ (subclass X s k)).toReal
          * (∫ ω, Y ω ∂(μ[|{ω | Z ω = true} ∩ subclass X s k])
              - ∫ ω, Y ω ∂(μ[|{ω | Z ω = false} ∩ subclass X s k])) := by
  sorry

/-- **Exact subclassification on the propensity score identifies the average causal
effect** (Ding §11.1.2, from Theorem 11.1): stratifying on `e(X)` — a scalar — is as good
as stratifying on the whole covariate, provided each level set of `e` is taken as one
subclass. -/
theorem subclassEstimand_propensity_eq_ate [IsProbabilityMeasure μ] [DecidableEq 𝒳]
    [Fintype 𝒦] (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ) (s : 𝒳 → 𝒦)
    -- USER-INPUT: the subclass map is exactly the propensity score, i.e. two covariate
    -- values share a subclass iff they share a propensity value; Ding §11.1.2
    (hs : ∀ x x', s x = s x' ↔ propensity μ Z X x = propensity μ Z X x') :
    subclassEstimand μ Z X (obs Z y1 y0) s = ate μ y1 y0 := by
  sorry

end StatLean.CausalInference
