import StatLean.CausalInference.Core.PopulationDefs
import StatLean.CausalInference.ForMathlib.CondAlgebra

/-!
# Selection bias — why the naive comparison is not a causal effect

The decomposition that motivates every identification assumption:

$$\underbrace{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}_{\tau_{\mathrm{PF}}}
 =\underbrace{\mathbb E[Y(1)-Y(0)\mid Z=1]}_{\tau_T}
 +\underbrace{\mathbb E[Y(0)\mid Z=1]-\mathbb E[Y(0)\mid Z=0]}_{\text{selection bias}}.$$

The prima facie (observed) contrast equals the effect on the treated plus a term that
compares the two arms on the *same* potential outcome; the latter vanishes precisely when
the arms are comparable, which is what randomization or ignorability delivers.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §10.2 (pp. 141–142): the prima facie effect, the
two selection-bias decompositions, and eqs. (10.1)–(10.2) showing that
`Z ⫫ {Y(1),Y(0)}` collapses `τ_PF = τ_T = τ_C = τ`. The decompositions are unnumbered
displays in the text. (`Ding §10.2`.)

**Proof formalization notes.** The two decompositions are algebraic identities of
conditional integrals once `E[Y | Z = 1] = E[Y(1) | Z = 1]` (consistency on the treated
arm) is available; that step is `integral_cond_treated_obs_eq`. The unconfounded corollary
uses independence *unconditionally* (no covariate), which is the randomized-experiment
case `X` constant — stated here with an explicit `IndepFun` hypothesis rather than
through `Unconfounded` so that it applies verbatim to a completely randomized experiment.

**Bibliographic comments.** The decomposition is the population version of the argument in
D. B. Rubin, "Estimating causal effects of treatments in randomized and nonrandomized
studies," *J. Educ. Psychol.* **66** (1974), 688–701.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ}

/-- On the treated arm the observed outcome has the treated potential outcome's
conditional mean (consistency, Ding Assumption 2.2). -/
theorem integral_cond_treated_obs_eq :
    ∫ ω, obs Z y1 y0 ω ∂(μ[|treatedEvent Z]) = ∫ ω, y1 ω ∂(μ[|treatedEvent Z]) := by
  sorry

/-- On the control arm the observed outcome has the control potential outcome's
conditional mean. -/
theorem integral_cond_control_obs_eq :
    ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]) = ∫ ω, y0 ω ∂(μ[|{ω | Z ω = false}]) := by
  sorry

/-- **Selection-bias decomposition** (Ding §10.2): the prima facie effect is the effect on
the treated plus the between-arm difference in the *control* potential outcome. -/
theorem primaFacie_eq_att_add_selectionBias :
    primaFacie μ Z (obs Z y1 y0)
      = att μ Z y1 y0
        + (∫ ω, y0 ω ∂(μ[|treatedEvent Z]) - ∫ ω, y0 ω ∂(μ[|{ω | Z ω = false}])) := by
  sorry

/-- **Selection-bias decomposition, control version** (Ding §10.2): the prima facie effect
is the effect on the controls plus the between-arm difference in the *treated* potential
outcome. -/
theorem primaFacie_eq_atc_add_selectionBias :
    primaFacie μ Z (obs Z y1 y0)
      = atc μ Z y1 y0
        + (∫ ω, y1 ω ∂(μ[|treatedEvent Z]) - ∫ ω, y1 ω ∂(μ[|{ω | Z ω = false}])) := by
  sorry

/-- **Randomization removes selection bias** (Ding eqs. (10.1)–(10.2)): if the treatment
is independent of the potential outcomes, the prima facie effect *is* the average causal
effect. This is the population statement of why randomized experiments identify `τ`. -/
theorem primaFacie_eq_ate_of_indep [IsProbabilityMeasure μ]
    -- USER-INPUT: the treatment is independent of the potential outcomes (randomization);
    -- Ding eq. (10.1)
    (hindep : IndepFun (fun ω => (y1 ω, y0 ω)) Z μ)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z)
    -- USER-INPUT: integrable potential outcomes; Ding assumes finite means
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both arms have positive probability; else a conditional mean is a junk value
    (hT : μ (treatedEvent Z) ≠ 0) (hC : μ {ω | Z ω = false} ≠ 0) :
    primaFacie μ Z (obs Z y1 y0) = ate μ y1 y0 := by
  sorry

/-- Under randomization the three estimands coincide (Ding eq. (10.2)). -/
theorem att_eq_ate_of_indep [IsProbabilityMeasure μ]
    (hindep : IndepFun (fun ω => (y1 ω, y0 ω)) Z μ)
    (hy1 : Measurable y1) (hy0 : Measurable y0) (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hT : μ (treatedEvent Z) ≠ 0) :
    att μ Z y1 y0 = ate μ y1 y0 := by
  sorry

/-- **`ATE` as the prevalence-weighted average of `ATT` and `ATC`** (Ding §10.2):
`τ = P(Z = 1)·τ_T + P(Z = 0)·τ_C`. -/
theorem ate_eq_prob_smul_att_add_atc [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the treatment; user-supplied data
    (hZ : Measurable Z)
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ) :
    ate μ y1 y0
      = (μ (treatedEvent Z)).toReal * att μ Z y1 y0
        + (μ {ω | Z ω = false}).toReal * atc μ Z y1 y0 := by
  sorry

end StatLean.CausalInference
