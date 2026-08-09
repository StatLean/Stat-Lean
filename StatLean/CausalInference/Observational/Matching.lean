import StatLean.CausalInference.Observational.Standardization

/-!
# Matching — exact matching, and the bias of inexact matches

Matching imputes each treated unit's missing control outcome by the outcome of a matched
control. Two facts govern its behaviour.

* **Exact matching balances the covariate**, so the imputation is unbiased: if the matched
  control has the *same* covariate value, its expected outcome is the same regression
  function `m₀(x)`.
* **Inexact matching leaves a bias** equal to the discrepancy of the control regression
  function between the two covariate values, `m₀(Xᵢ) - m₀(X_{j(i)})`. If `m₀` is
  `L`-Lipschitz this is at most `L·d(Xᵢ, X_{j(i)})` — so the bias is controlled by the
  match quality, which is the entire justification for bias-corrected matching.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). ch. 15 (*Matching in Observational Studies*):
§15.1 (pp. 203–204, incl. the footnote showing that an exactly matched study can be
analyzed as a matched-pair experiment, so that ch. 7's results apply — no theorem number);
§15.3.1 (pp. 206–207: the matching estimator `τ̂^m = n⁻¹∑{Ŷᵢ(1) - Ŷᵢ(0)}` with
`Ŷᵢ(0) = M⁻¹∑_{k∈Jᵢ}Y_k`, and the bias-correction term
`B̂ᵢ = M⁻¹∑_{k∈Jᵢ}{μ̂₀(Xᵢ) - μ̂₀(X_k)}`), **Proposition 15.1** (p. 207: the linear
expansion of the bias-corrected estimator). (`Ding ch. 15; §15.1; §15.3.1;
Proposition 15.1`.) Matching for balance and matching estimators are chs. 15 and 18 of
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015. (`IR chs. 15, 18`.)

**Scope.** Formalized here are the **population/estimand-level** statements: exact matching
recovers the control regression function, and the inexact-matching bias equals the `m₀`
discrepancy and is Lipschitz-controlled. The finite-sample matching estimator with `M`
nearest neighbours, its bias-corrected version and Propositions 15.1–15.4 are *estimation*
results whose content is the asymptotic behaviour of the matching discrepancy; they are out
of scope for this release, which stops at identification.

**Proof formalization notes.** A matching is a map `j : Ω → Ω` sending each unit to its
matched partner (`matchedControl`); exactness is `X (j ω) = X ω`. The unbiasedness
statement is then a direct corollary of `Ignorability`'s cell-mean bridge: the matched
partner is drawn from the same covariate cell, whose control arm has mean `m₀(x)`. The
Lipschitz bound is a pointwise estimate with no probabilistic content — it is stated over a
`PseudoMetricSpace` covariate so that "match quality" has a meaning.

**Bibliographic comments.** The bias-corrected matching estimator and its asymptotics are
A. Abadie and G. W. Imbens, "Large sample properties of matching estimators for average
treatment effects," *Econometrica* **74** (2006), 235–267, and "Bias-corrected matching
estimators for average treatment effects," *J. Bus. Econom. Statist.* **29** (2011), 1–11.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- A **matching** is exact when each unit's matched partner has the same covariate value
(Ding §15.1). -/
def IsExactMatching (X : Ω → 𝒳) (j : Ω → Ω) : Prop := ∀ ω, X (j ω) = X ω

/-- Under an exact matching, the matched partner lies in the same covariate cell — the
covariate is perfectly balanced by construction (Ding §15.1). -/
theorem cell_matched_eq (X : Ω → 𝒳) {j : Ω → Ω} (h : IsExactMatching X j) (ω : Ω) :
    cell X (X (j ω)) = cell X (X ω) := by
  sorry

/-- **Exact matching imputes the right counterfactual mean** (Ding §15.1): the control arm
of the matched unit's cell has mean `m₀(X ω)`, which under ignorability is the conditional
mean of the control potential outcome for that unit's cell. So the exactly matched
imputation is unbiased. -/
theorem cellMean_matched_eq_cate [IsProbabilityMeasure μ] {j : Ω → Ω}
    -- USER-INPUT: the matching is exact; Ding §15.1
    (hmatch : IsExactMatching X j)
    -- USER-INPUT: strong ignorability; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: overlap; Ding §11.2.1
    (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi0 : Integrable y0 μ) {ω : Ω}
    -- USER-INPUT: the unit's covariate cell carries mass
    (hcell : μ (cell X (X ω)) ≠ 0) :
    cellMean μ Z X (obs Z y1 y0) false (X (j ω))
      = ∫ ω', y0 ω' ∂(μ[|cell X (X ω)]) := by
  sorry

/-- **Exact matching identifies the effect on the treated** (Ding §15.1, via the matched-pair
reading): averaging the matched contrasts over the treated units gives `τ_T`. -/
theorem att_eq_integral_matched_contrast [IsProbabilityMeasure μ] {j : Ω → Ω}
    (hmatch : IsExactMatching X j) (hu : Unconfounded μ Z y1 y0 X) (hpos : Positive μ Z X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: some unit is treated; Ding ch. 13
    (hT : μ (treatedEvent Z) ≠ 0) :
    att μ Z y1 y0
      = ∫ ω, (obs Z y1 y0 ω - cellMean μ Z X (obs Z y1 y0) false (X (j ω)))
          ∂(μ[|treatedEvent Z]) := by
  sorry

/-- The **matching bias** of an inexact match at a unit: the discrepancy of the control
regression function between the unit's covariate value and its match's
(Ding §15.3.1, the `B̂ᵢ` term). -/
noncomputable def matchingBias (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ)
    (j : Ω → Ω) (ω : Ω) : ℝ :=
  cellMean μ Z X Y false (X ω) - cellMean μ Z X Y false (X (j ω))

/-- An exact match has no bias (Ding §15.1). -/
theorem matchingBias_eq_zero_of_exact {j : Ω → Ω} (h : IsExactMatching X j) (Y : Ω → ℝ)
    (ω : Ω) :
    matchingBias μ Z X Y j ω = 0 := by
  sorry

/-- **The matching bias is controlled by the match quality** (Ding §15.3.1; Abadie–Imbens):
if the control regression function is `L`-Lipschitz in the covariate, the bias at each unit
is at most `L` times the distance between the unit and its match. This is the estimate that
justifies bias-corrected matching. -/
theorem abs_matchingBias_le [PseudoMetricSpace 𝒳] {j : Ω → Ω} {L : ℝ} {Y : Ω → ℝ}
    -- USER-INPUT: the control regression function is Lipschitz; the smoothness condition
    -- of Ding §15.3.1 (Abadie–Imbens)
    (hL : LipschitzWith (Real.toNNReal L) (cellMean μ Z X Y false))
    -- LEAN-ONLY: a nonnegative Lipschitz constant, so `Real.toNNReal L` is `L`
    (hL0 : 0 ≤ L) (ω : Ω) :
    |matchingBias μ Z X Y j ω| ≤ L * dist (X ω) (X (j ω)) := by
  sorry

end StatLean.CausalInference
