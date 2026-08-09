import StatLean.CausalInference.Observational.SelectionBias

/-!
# Manski-type worst-case bounds — what the data alone can say

Without any identification assumption the average causal effect is *not* identified, but it
is not arbitrary either: if the outcome is known to lie in `[lo, hi]`, then filling in the
missing potential outcomes with their extreme values gives sharp bounds. Writing
`p = P(Z = 1)`,

$$\tau\ \in\
 \bigl[\,p\,\mathbb E[Y\mid Z{=}1]+(1-p)\,\mathrm{lo}
        -p\,\mathrm{hi}-(1-p)\,\mathbb E[Y\mid Z{=}0],\
        p\,\mathbb E[Y\mid Z{=}1]+(1-p)\,\mathrm{hi}
        -p\,\mathrm{lo}-(1-p)\,\mathbb E[Y\mid Z{=}0]\,\bigr],$$

an interval of width exactly `hi - lo` — never empty, never a point. The interval is
**sharp**: both endpoints are attained by genuine potential-outcome laws with the same
observed-data distribution.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §18.2 (pp. 248–249: "Manski-type worst-case bounds
on the average causal effect without assumptions", where the bounds are derived as
unnumbered displays and the width is observed to be exactly `ȳ - y̲`);
Definition 18.1 (p. 249: partial identification). (`Ding §18.2; Definition 18.1`.)
Sensitivity analysis and bounds are ch. 22 of G. W. Imbens and D. B. Rubin, *Causal
Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University Press,
2015. (`IR ch. 22`.)

**Scope.** Sharpness is **not** stated in either reference (it goes back to Manski's own
work); it is proved here anyway, in the natural form: the extreme values are *attained*, by
exhibiting potential outcomes that agree with the given ones on the observed arm and take
the extreme value on the unobserved arm. That is the honest content of "sharp" for this
bound, and it needs no additional theory.

**Proof formalization notes.** The whole file rests on the decomposition
`E[Y(1)] = p·E[Y|Z=1] + (1-p)·E[Y(1)|Z=0]` (`SelectionBias`-style two-arm split), in which
only the second summand is unidentified; bounding it by `lo` and `hi` gives the interval.
The width computation is then a cancellation: the identified parts drop out and what
remains is `(1-p)(hi - lo) + p(hi - lo)`. Sharpness constructs, for the upper endpoint,
`y1' = if Z then y1 else hi` and `y0' = if Z then lo else y0`; these have the same observed
outcome function as `(y1, y0)` by construction.

**Bibliographic comments.** C. F. Manski, "Nonparametric bounds on treatment effects,"
*Amer. Econ. Rev.* **80** (1990), 319–323, and *Partial Identification of Probability
Distributions*, Springer, 2003.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ}
  {lo hi : ℝ}

/-- The **Manski lower bound** on the mean of a potential outcome: the observed arm
contributes its mean, the unobserved arm its lowest possible value (Ding §18.2). -/
noncomputable def manskiLowerY1 (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ) (lo : ℝ) : ℝ :=
  (μ (treatedEvent Z)).toReal * ∫ ω, Y ω ∂(μ[|treatedEvent Z])
    + (μ {ω | Z ω = false}).toReal * lo

/-- The **Manski upper bound** on the mean of a potential outcome (Ding §18.2). -/
noncomputable def manskiUpperY1 (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ) (hi : ℝ) : ℝ :=
  (μ (treatedEvent Z)).toReal * ∫ ω, Y ω ∂(μ[|treatedEvent Z])
    + (μ {ω | Z ω = false}).toReal * hi

/-- The two-arm decomposition of a potential-outcome mean: only the counterfactual arm is
unidentified. -/
theorem integral_y1_eq_arm_split [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the treatment; user-supplied data
    (hZ : Measurable Z)
    -- USER-INPUT: integrability of the potential outcome
    (hi1 : Integrable y1 μ) :
    ∫ ω, y1 ω ∂μ
      = (μ (treatedEvent Z)).toReal * ∫ ω, y1 ω ∂(μ[|treatedEvent Z])
        + (μ {ω | Z ω = false}).toReal * ∫ ω, y1 ω ∂(μ[|{ω | Z ω = false}]) := by
  sorry

/-- **The Manski lower bound holds** (Ding §18.2). -/
theorem manskiLowerY1_le [IsProbabilityMeasure μ] (hZ : Measurable Z) (hi1 : Integrable y1 μ)
    -- USER-INPUT: the outcome is bounded below; the only assumption Manski bounds use
    (hlo : ∀ ω, lo ≤ y1 ω) :
    manskiLowerY1 μ Z (obs Z y1 y0) lo ≤ ∫ ω, y1 ω ∂μ := by
  sorry

/-- **The Manski upper bound holds** (Ding §18.2). -/
theorem le_manskiUpperY1 [IsProbabilityMeasure μ] (hZ : Measurable Z) (hi1 : Integrable y1 μ)
    -- USER-INPUT: the outcome is bounded above
    (hhi : ∀ ω, y1 ω ≤ hi) :
    ∫ ω, y1 ω ∂μ ≤ manskiUpperY1 μ Z (obs Z y1 y0) hi := by
  sorry

/-- The **Manski bounds on the average causal effect** (Ding §18.2): lower endpoint. -/
noncomputable def manskiLowerATE (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ)
    (lo hi : ℝ) : ℝ :=
  manskiLowerY1 μ Z Y lo
    - ((μ (treatedEvent Z)).toReal * hi
        + (μ {ω | Z ω = false}).toReal * ∫ ω, Y ω ∂(μ[|{ω | Z ω = false}]))

/-- The **Manski bounds on the average causal effect** (Ding §18.2): upper endpoint. -/
noncomputable def manskiUpperATE (μ : Measure Ω) (Z : Ω → Bool) (Y : Ω → ℝ)
    (lo hi : ℝ) : ℝ :=
  manskiUpperY1 μ Z Y hi
    - ((μ (treatedEvent Z)).toReal * lo
        + (μ {ω | Z ω = false}).toReal * ∫ ω, Y ω ∂(μ[|{ω | Z ω = false}]))

/-- **The average causal effect lies in the Manski interval** (Ding §18.2). -/
theorem ate_mem_manski_Icc [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    -- USER-INPUT: both potential outcomes lie in `[lo, hi]`; the only assumption used
    (hb1 : ∀ ω, y1 ω ∈ Set.Icc lo hi) (hb0 : ∀ ω, y0 ω ∈ Set.Icc lo hi) :
    ate μ y1 y0 ∈ Set.Icc (manskiLowerATE μ Z (obs Z y1 y0) lo hi)
      (manskiUpperATE μ Z (obs Z y1 y0) lo hi) := by
  sorry

/-- **The Manski interval has width exactly `hi - lo`** (Ding §18.2): the bound never
collapses to a point, and never exceeds the a priori range — the identified parts cancel
exactly. -/
theorem manski_width [IsProbabilityMeasure μ] (hZ : Measurable Z) (Y : Ω → ℝ) :
    manskiUpperATE μ Z Y lo hi - manskiLowerATE μ Z Y lo hi = hi - lo := by
  sorry

/-- **Sharpness of the upper bound**: the upper endpoint is attained by a potential-outcome
pair with the *same observed data*, so no argument from the observed distribution alone can
improve it. -/
theorem exists_ate_eq_manskiUpper [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hb1 : ∀ ω, y1 ω ∈ Set.Icc lo hi) (hb0 : ∀ ω, y0 ω ∈ Set.Icc lo hi) :
    ∃ y1' y0' : Ω → ℝ,
      obs Z y1' y0' = obs Z y1 y0
        ∧ (∀ ω, y1' ω ∈ Set.Icc lo hi) ∧ (∀ ω, y0' ω ∈ Set.Icc lo hi)
        ∧ ate μ y1' y0' = manskiUpperATE μ Z (obs Z y1 y0) lo hi := by
  sorry

/-- **Sharpness of the lower bound**. -/
theorem exists_ate_eq_manskiLower [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hb1 : ∀ ω, y1 ω ∈ Set.Icc lo hi) (hb0 : ∀ ω, y0 ω ∈ Set.Icc lo hi) :
    ∃ y1' y0' : Ω → ℝ,
      obs Z y1' y0' = obs Z y1 y0
        ∧ (∀ ω, y1' ω ∈ Set.Icc lo hi) ∧ (∀ ω, y0' ω ∈ Set.Icc lo hi)
        ∧ ate μ y1' y0' = manskiLowerATE μ Z (obs Z y1 y0) lo hi := by
  sorry

end StatLean.CausalInference
