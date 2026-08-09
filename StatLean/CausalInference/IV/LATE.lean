import StatLean.CausalInference.IV.ComplianceTypes
import StatLean.CausalInference.ForMathlib.CondAlgebra

/-!
# The LATE / CACE theorem — the Wald ratio identifies the complier average effect

The flagship instrumental-variables result. Under random assignment, monotonicity and the
exclusion restriction, the two intention-to-treat contrasts decompose as

$$\tau_D=\Pr(\text{complier}),\qquad
  \tau_Y=\Pr(\text{complier})\cdot\mathbb E[Y(1)-Y(0)\mid\text{complier}],$$

so that whenever the instrument is relevant (`τ_D ≠ 0`) the **Wald ratio** identifies the
complier average causal effect:

$$\frac{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}
       {\mathbb E[D\mid Z=1]-\mathbb E[D\mid Z=0]}
 =\mathbb E[Y(1)-Y(0)\mid D(1)>D(0)].$$

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). eq. (21.4) (p. 284: the first stage equals the
complier proportion, under Assumption 21.2); eq. (21.3) (p. 283: the reduced form is the
complier proportion times the complier effect, under Assumptions 21.2–21.3, from the
four-term decomposition eq. (21.1)); **Theorem 21.1** (p. 284: `τ_c = τ_Y/τ_D` when
`τ_D ≠ 0`); **Corollary 21.1** (p. 285: the observable Wald form, under Assumptions
21.1–21.3); Theorem 22.1 (§22.1, p. 302: identification of the type proportions and the
type-specific outcome means). (`Ding eqs. (21.3)–(21.4); Theorem 21.1; Corollary 21.1;
Theorem 22.1`.) The corresponding development is G. W. Imbens and D. B. Rubin, *Causal
Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University Press,
2015, chs. 23–24. (`IR chs. 23–24`.)

**Proof formalization notes.** The decompositions are proved in the order the book uses:
first move from observed arm means to potential-outcome means using random assignment
(`ittContrast_eq_integral_sub`, an application of independence), then split the resulting
expectation over the four compliance-type events, then kill the defier term with
monotonicity and the always/never-taker terms with the exclusion restriction. The ratio
theorem is then division; relevance `τ_D ≠ 0` is a genuine hypothesis and is exactly what
fails for a weak instrument.

**Bibliographic comments.** G. W. Imbens and J. D. Angrist, "Identification and estimation
of local average treatment effects," *Econometrica* **62** (1994), 467–475;
J. D. Angrist, G. W. Imbens and D. B. Rubin, "Identification of causal effects using
instrumental variables," *J. Amer. Statist. Assoc.* **91** (1996), 444–455 (with the
discussion in which the "LATE" and "CACE" names are debated).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z d1 d0 : Ω → Bool}
  {y1 y0 : Ω → ℝ}

/-- **Random assignment turns an arm contrast into a potential-outcome contrast**
(Ding Assumption 21.1): the intention-to-treat contrast of the observed outcome is the
average difference of the potential outcomes. -/
theorem ittContrast_eq_integral_sub [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment of the instrument; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    -- USER-INPUT: integrable potential outcomes; Ding assumes finite means
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both instrument arms have positive probability; Ding §21.2
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (obs Z y1 y0) = ∫ ω, (y1 ω - y0 ω) ∂μ := by
  sorry

/-- The same identity for the observed *treatment*: the first stage is the average
difference of the potential treatments. -/
theorem ittContrast_treat_eq_integral_sub [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω))
      = ∫ ω, (ind (d1 ω) - ind (d0 ω)) ∂μ := by
  sorry

/-- **The first stage is the complier proportion** (Ding eq. (21.4)): under monotonicity,
`E[D | Z = 1] - E[D | Z = 0] = P(complier)`. -/
theorem firstStage_eq_prob_complier [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    -- USER-INPUT: monotonicity / no defiers; Ding Assumption 21.2
    (hmono : NoDefiers d1 d0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω))
      = (μ (typeSet d1 d0 ComplianceType.complier)).toReal := by
  sorry

/-- **The reduced form is the complier proportion times the complier effect**
(Ding eq. (21.3)): under monotonicity and the exclusion restriction, the always takers and
never takers contribute nothing to the intention-to-treat effect. -/
theorem reducedForm_eq_prob_complier_mul_cace [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 y1 y0)
    -- USER-INPUT: monotonicity; Ding Assumption 21.2
    (hmono : NoDefiers d1 d0)
    -- USER-INPUT: the exclusion restriction; Ding Assumption 21.3
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (obs Z y1 y0)
      = (μ (typeSet d1 d0 ComplianceType.complier)).toReal * cace μ d1 d0 y1 y0 := by
  sorry

/-- **The LATE / CACE theorem** (Ding Theorem 21.1, p. 284): when the instrument is
relevant, the ratio of the reduced form to the first stage is the complier average causal
effect. -/
theorem cace_eq_ittContrast_div [IsProbabilityMeasure μ]
    -- USER-INPUT: the three IV assumptions; Ding Assumptions 21.1–21.3
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    -- USER-INPUT: instrument relevance `τ_D ≠ 0`; Ding Theorem 21.1 (fails for a weak
    -- instrument)
    (hrel : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) ≠ 0) :
    cace μ d1 d0 y1 y0
      = ittContrast μ Z (obs Z y1 y0) / ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) := by
  sorry

/-- **The Wald ratio in observable form** (Ding Corollary 21.1, p. 285): written out, the
identification formula uses only the observed outcome and treatment in the two instrument
arms. -/
theorem cace_eq_wald_ratio [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    (hrel : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) ≠ 0) :
    cace μ d1 d0 y1 y0
      = (∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = true}])
          - ∫ ω, obs Z y1 y0 ω ∂(μ[|{ω | Z ω = false}]))
        / (∫ ω, ind (obsTreat Z d1 d0 ω) ∂(μ[|{ω | Z ω = true}])
          - ∫ ω, ind (obsTreat Z d1 d0 ω) ∂(μ[|{ω | Z ω = false}])) := by
  sorry

/-- **Identification of the never-taker proportion** (Ding Theorem 22.1, p. 302):
`π_n = P(D = 0 | Z = 1)`. -/
theorem prob_neverTaker_eq [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) :
    (μ (typeSet d1 d0 ComplianceType.neverTaker)).toReal
      = ((μ[|{ω | Z ω = true}]) {ω | obsTreat Z d1 d0 ω = false}).toReal := by
  sorry

/-- **Identification of the always-taker proportion** (Ding Theorem 22.1, p. 302):
`π_a = P(D = 1 | Z = 0)`. -/
theorem prob_alwaysTaker_eq [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    (μ (typeSet d1 d0 ComplianceType.alwaysTaker)).toReal
      = ((μ[|{ω | Z ω = false}]) {ω | obsTreat Z d1 d0 ω = true}).toReal := by
  sorry

end StatLean.CausalInference
