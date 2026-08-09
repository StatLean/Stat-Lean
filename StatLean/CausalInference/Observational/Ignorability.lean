import StatLean.CausalInference.Core.PopulationDefs
import StatLean.CausalInference.ForMathlib.CondAlgebra

/-!
# Unconfoundedness — what it buys inside a covariate cell

The bridge between the assumption `{Y(1), Y(0)} ⫫ Z | X` and the identification formulas:
inside a covariate cell, the conditional mean of a potential outcome does not depend on
which arm one conditions on, i.e. **the arm regression function recovers the potential
outcome mean**,

$$m_z(x)=\mathbb E[Y\mid Z=z,X=x]=\mathbb E[Y(z)\mid X=x].$$

This is the only place where independence is used; every later identification theorem
(standardization, IPW, AIPW, ATT) consumes this file's conclusions.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Assumption 10.1 (ignorability `Y(z) ⫫ Z | X`,
eq. (10.10)), Assumption 10.2 (strong ignorability `{Y(1),Y(0)} ⫫ Z | X`, eq. (10.11)),
and eqs. (10.3)–(10.4) (the mean-ignorability hypotheses of Theorem 10.1).
(`Ding Assumptions 10.1–10.2; §10.3`.) The unconfoundedness terminology and its role in
observational studies is that of G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015, Part III.
(`IR Part III`.)

**Proof formalization notes.** With a discrete covariate, `Unconfounded` is cell-wise
independence under `μ[|{X = x}]` (see `Core.PopulationDefs`), so each result here is
`ForMathlib.CondAlgebra.integral_cond_arm_eq_of_indepFun` applied inside a cell, after
rewriting `μ[|{Z = z} ∩ {X = x}]` as `(μ[|{X = x}])[|{Z = z}]` — that rewriting
(`cond_cond_eq_cond_inter`) is the first lemma below. Observed outcomes agree with the
relevant potential outcome on each arm, which is what lets `cellMean` of the *observed*
outcome be replaced by a potential-outcome mean.

**Bibliographic comments.** P. R. Rosenbaum and D. B. Rubin, "The central role of the
propensity score in observational studies for causal effects," *Biometrika* **70** (1983),
41–55, introduce strong ignorability.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳]
  {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- Conditioning twice is conditioning on the intersection. -/
theorem cond_cond_eq_cond_inter (s t : Set Ω)
    -- USER-INPUT: measurability of the inner conditioning event
    (hs : MeasurableSet s) :
    (μ[|s])[|t] = μ[|t ∩ s] := by
  sorry

/-- On the treated arm the observed outcome is the treated potential outcome. -/
theorem obs_eqOn_treated : Set.EqOn (obs Z y1 y0) y1 {ω | Z ω = true} := by
  sorry

/-- On the control arm the observed outcome is the control potential outcome. -/
theorem obs_eqOn_control : Set.EqOn (obs Z y1 y0) y0 {ω | Z ω = false} := by
  sorry

/-- The arm regression function of the *observed* outcome is the arm regression function
of the corresponding *potential* outcome — no assumption needed, just consistency
(Ding Assumption 2.2). -/
theorem cellMean_obs_eq (z : Bool) (x : 𝒳) :
    cellMean μ Z X (obs Z y1 y0) z x
      = cellMean μ Z X (if z then y1 else y0) z x := by
  sorry

/-- **Unconfoundedness identifies the cell means** (Ding Assumption 10.2 ⇒ eq. (10.5)):
inside a covariate cell of positive probability, the treated arm's regression function
equals the conditional mean of the treated potential outcome. -/
theorem cellMean_true_eq_of_unconfounded [IsProbabilityMeasure μ]
    -- USER-INPUT: strong ignorability `{Y(1),Y(0)} ⫫ Z | X`; Ding Assumption 10.2
    (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrability of the potential outcome; Ding assumes finite means
    (hint : Integrable y1 μ) {x : 𝒳}
    -- USER-INPUT: a covariate cell of positive probability
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) > 0`; Ding §11.2.1 (else the treated arm is empty)
    (hpos : (μ[|cell X x]) (treatedEvent Z) ≠ 0) :
    cellMean μ Z X (obs Z y1 y0) true x = ∫ ω, y1 ω ∂(μ[|cell X x]) := by
  sorry

/-- **Unconfoundedness identifies the cell means**, control arm (Ding Assumption 10.2 ⇒
eq. (10.6)). -/
theorem cellMean_false_eq_of_unconfounded [IsProbabilityMeasure μ]
    (hu : Unconfounded μ Z y1 y0 X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y0 μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0)
    -- USER-INPUT: positivity `e(x) < 1`; Ding §11.2.1 (else the control arm is empty)
    (hpos : (μ[|cell X x]) {ω | Z ω = false} ≠ 0) :
    cellMean μ Z X (obs Z y1 y0) false x = ∫ ω, y0 ω ∂(μ[|cell X x]) := by
  sorry

/-- **Strong ignorability implies ignorability for each arm** (Ding Assumption 10.2 ⇒
Assumption 10.1). -/
theorem Unconfounded.ignorable_left (hu : Unconfounded μ Z y1 y0 X)
    -- USER-INPUT: measurability of the potential outcomes; needed to project the pair
    (hy1 : Measurable y1) (hy0 : Measurable y0) :
    Ignorable μ Z y1 X := by
  sorry

/-- **Strong ignorability implies ignorability for the control arm.** -/
theorem Unconfounded.ignorable_right (hu : Unconfounded μ Z y1 y0 X)
    (hy1 : Measurable y1) (hy0 : Measurable y0) :
    Ignorable μ Z y0 X := by
  sorry

/-- **Ignorability implies mean ignorability** (Ding Assumption 10.1 ⇒ eqs. (10.3)–(10.4)):
the hypothesis actually used by the standardization theorem is weaker than independence. -/
theorem MeanIgnorable_of_ignorable [IsProbabilityMeasure μ]
    (hi : Ignorable μ Z y1 X)
    (hy1 : Measurable y1) (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable y1 μ)
    -- USER-INPUT: positivity in every cell, so that both arm means are genuine averages;
    -- Ding §11.2.1
    (hpos : Positive μ Z X) :
    MeanIgnorable μ Z y1 X := by
  sorry

end StatLean.CausalInference
