import StatLean.CausalInference.IV.ComplianceTypes
import StatLean.CausalInference.ForMathlib.CondAlgebra

/-!
# Instrumental inequalities — the testable implications of the IV model

The IV assumptions are not vacuous: for a **binary** outcome they imply four inequalities
among quantities that are functions of the observed distribution alone,

$$\mathbb E[Q\mid Z=1]-\mathbb E[Q\mid Z=0]\ \ge\ 0
  \qquad\text{for } Q\in\{DY,\;D(1-Y),\;(D-1)Y,\;D+Y-DY\}.$$

A violation in data refutes the conjunction of random assignment, monotonicity and the
exclusion restriction — so unlike most identification assumptions, this package is
partially falsifiable.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). **Theorem 22.2** (Instrumental Variable
Inequalities, §22.2, p. 304, eq. (22.1)), under Assumptions 21.1–21.3 with a binary
outcome. (`Ding Theorem 22.2`.) Related discussion of testable implications is in
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, ch. 25. (`IR ch. 25`.)

**Proof formalization notes.** Each inequality is proved by the same three-step recipe:
random assignment replaces the arm-conditional means by unconditional means of the
corresponding potential quantities; the mixture over compliance types is then split;
monotonicity kills the defier stratum and the exclusion restriction makes the always- and
never-taker strata cancel between the two arms. What remains is the complier stratum with
a sign that is forced by `0 ≤ Y ≤ 1` — which is where binariness of the outcome is used,
and why the inequalities have no unbounded-outcome analogue. The four differences equal
`P(complier)` times, respectively, `E[Y(1)|C]`, `E[1-Y(1)|C]`, `E[Y(0)|C]` (with the sign
flip built into `(D-1)Y`) and `E[1-Y(0)|C]`; those exact identities are stated first and
the inequalities follow.

**Bibliographic comments.** The inequalities are due to A. Balke and J. Pearl, "Bounds on
treatment effects from studies with imperfect compliance," *J. Amer. Statist. Assoc.*
**92** (1997), 1171–1176, and (in a different form) B. Pearl, "On the testability of
causal models with latent and instrumental variables," *UAI* (1995), 435–443.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z d1 d0 b1 b0 : Ω → Bool}

/-- The observed **binary** outcome `Y = Y(Z)` under a binary-outcome IV model. -/
def obsBool (Z b1 b0 : Ω → Bool) : Ω → Bool := fun ω => if Z ω then b1 ω else b0 ω

/-- **First IV inequality, exact form** (Ding Theorem 22.2, `Q = DY`): the arm contrast
equals the complier proportion times the complier mean of `Y(1)`. -/
theorem ittContrast_treat_mul_outcome [IsProbabilityMeasure μ]
    -- USER-INPUT: random assignment; Ding Assumption 21.1
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    -- USER-INPUT: monotonicity; Ding Assumption 21.2
    (hmono : Monotone d1 d0)
    -- USER-INPUT: the exclusion restriction; Ding Assumption 21.3
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    -- USER-INPUT: measurability of the model variables; user-supplied data
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    -- USER-INPUT: both instrument arms have positive probability; Ding §21.2
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω))
      = (μ (typeSet d1 d0 ComplianceType.complier)).toReal
          * ∫ ω, ind (b1 ω) ∂(μ[|typeSet d1 d0 ComplianceType.complier]) := by
  sorry

/-- **First instrumental inequality** (Ding Theorem 22.2, eq. (22.1), `Q = DY`). -/
theorem instrumentalInequality_DY [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : Monotone d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω)) := by
  sorry

/-- **Second instrumental inequality** (Ding Theorem 22.2, `Q = D(1-Y)`). -/
theorem instrumentalInequality_D_one_sub_Y [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : Monotone d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z
          (fun ω => ind (obsTreat Z d1 d0 ω) * (1 - ind (obsBool Z b1 b0 ω))) := by
  sorry

/-- **Third instrumental inequality** (Ding Theorem 22.2, `Q = (D-1)Y`). -/
theorem instrumentalInequality_D_sub_one_Y [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : Monotone d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z
          (fun ω => (ind (obsTreat Z d1 d0 ω) - 1) * ind (obsBool Z b1 b0 ω)) := by
  sorry

/-- **Fourth instrumental inequality** (Ding Theorem 22.2, `Q = D + Y - DY`). -/
theorem instrumentalInequality_D_add_Y_sub_DY [IsProbabilityMeasure μ]
    (hrand : IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hmono : Monotone d1 d0)
    (hexcl : ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω)))
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    0 ≤ ittContrast μ Z
          (fun ω => ind (obsTreat Z d1 d0 ω) + ind (obsBool Z b1 b0 ω)
                      - ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω)) := by
  sorry

/-- **Falsifiability** (Ding §22.2): if any of the four observable contrasts is negative,
no IV model satisfying Assumptions 21.1–21.3 can have generated the data. Stated as the
contrapositive of the first inequality; the other three are analogous. -/
theorem not_ivModel_of_neg [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hb1 : Measurable b1) (hb0 : Measurable b0)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    -- USER-INPUT: an observed violation of the first inequality
    (hviol : ittContrast μ Z
        (fun ω => ind (obsTreat Z d1 d0 ω) * ind (obsBool Z b1 b0 ω)) < 0) :
    ¬ (IVRandomized μ Z d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω))
        ∧ Monotone d1 d0
        ∧ ExclusionRestriction d1 d0 (fun ω => ind (b1 ω)) (fun ω => ind (b0 ω))) := by
  sorry

end StatLean.CausalInference
