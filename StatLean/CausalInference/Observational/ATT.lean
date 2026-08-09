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

/-! ### Private toolkit

The same cell bookkeeping as in `AIPW`: arm weights as set indicators, integrability of
the weighted integrands, and the two arm partial means inside a covariate cell. -/

/-- Auxiliary: a conditional measure of a finite measure takes no infinite value. -/
private lemma cond_apply_ne_top' [IsFiniteMeasure μ] {c : Set Ω} (hc : MeasurableSet c)
    (t : Set Ω) : (μ[|c]) t ≠ ⊤ := by
  rcases eq_or_ne (μ c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · rw [cond_apply hc]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h) (measure_ne_top _ _)

/-- Auxiliary: integrability transfers to any conditional measure of a finite measure. -/
private lemma integrable_cond' {ν : Measure Ω} [IsFiniteMeasure ν] {c : Set Ω} {f : Ω → ℝ}
    (hf : Integrable f ν) : Integrable f (ν[|c]) := by
  rcases eq_or_ne (ν c) 0 with h | h
  · simp [cond_eq_zero_of_meas_eq_zero h]
  · exact (hf.integrableOn (s := c)).smul_measure (by simp [h])

/-- Multiplying by the treated weight is restricting to the treated event. -/
private lemma ind_mul_eq_indicator (Z : Ω → Bool) (f : Ω → ℝ) :
    (fun ω => ind (Z ω) * f ω) = Set.indicator {ω | Z ω = true} f := by
  funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]

/-- Multiplying by the control weight is restricting to the control event. -/
private lemma one_sub_ind_mul_eq_indicator (Z : Ω → Bool) (f : Ω → ℝ) :
    (fun ω => (1 - ind (Z ω)) * f ω) = Set.indicator {ω | Z ω = false} f := by
  funext ω; cases h : Z ω <;> simp [ind, Set.indicator, h]

/-- The observed outcome of two integrable potential outcomes is integrable. -/
private lemma integrable_obs' (hZ : Measurable Z) (hi1 : Integrable y1 μ)
    (hi0 : Integrable y0 μ) : Integrable (obs Z y1 y0) μ := by
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hf : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hrw : obs Z y1 y0
      = fun ω => Set.indicator {ω | Z ω = true} y1 ω + Set.indicator {ω | Z ω = false} y0 ω := by
    funext ω; cases h : Z ω <;> simp [obs, Set.indicator, h]
  rw [hrw]
  exact (hi1.indicator ht).add (hi0.indicator hf)

/-- A function of a finite covariate is bounded, hence integrable. -/
private lemma integrable_comp' [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω)) μ := by
  have hgm : Measurable fun ω => g (X ω) := (measurable_of_countable g).comp hX
  refine Integrable.mono' (integrable_const (∑ x : 𝒳, |g x|)) hgm.aestronglyMeasurable ?_
  filter_upwards with ω
  exact (le_of_eq (Real.norm_eq_abs _)).trans
    (Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (X ω)))

/-- A bounded function of the covariate times an integrable function is integrable. -/
private lemma integrable_comp_mul' [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ)
    {f : Ω → ℝ} (hf : Integrable f μ) : Integrable (fun ω => g (X ω) * f ω) μ := by
  have hgm : Measurable fun ω => g (X ω) := (measurable_of_countable g).comp hX
  refine hf.bdd_mul (c := ∑ x : 𝒳, |g x|) hgm.aestronglyMeasurable ?_
  filter_upwards with ω
  exact (le_of_eq (Real.norm_eq_abs _)).trans
    (Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (X ω)))

/-- The treated-arm partial mean inside a cell: the arm mass times the arm regression. -/
private lemma integral_ind_mul_cond_cell [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (hf : Integrable f μ) (x : 𝒳) :
    ∫ ω, ind (Z ω) * f ω ∂(μ[|cell X x])
      = propensity μ Z X x * cellMean μ Z X f true x := by
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have ht : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  rw [ind_mul_eq_indicator, integral_indicator ht,
    ← measureReal_mul_integral_cond (cond_apply_ne_top' hc _) f,
    cond_cond_eq_cond_inter' hc ht (measure_ne_top μ _), Set.inter_comm]
  rfl

/-- The control-arm partial mean inside a cell of positive mass. -/
private lemma integral_one_sub_ind_mul_cond_cell [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hZ : Measurable Z) (hX : Measurable X) (hf : Integrable f μ) {x : 𝒳}
    (hcell : μ (cell X x) ≠ 0) :
    ∫ ω, (1 - ind (Z ω)) * f ω ∂(μ[|cell X x])
      = (1 - propensity μ Z X x) * cellMean μ Z X f false x := by
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hfl : MeasurableSet {ω | Z ω = false} := hZ (measurableSet_singleton false)
  have hmass : ((μ[|cell X x]) {ω | Z ω = false}).toReal = 1 - propensity μ Z X x := by
    have hadd := cond_treated_add_cond_control (μ := μ) hX hZ hcell
    have hp : propensity μ Z X x = ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal := rfl
    have h2 : ((μ[|cell X x]) {ω | Z ω = false}).toReal
        = ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal := rfl
    rw [hp, h2]
    linarith
  rw [one_sub_ind_mul_eq_indicator, integral_indicator hfl,
    ← measureReal_mul_integral_cond (cond_apply_ne_top' hc _) f,
    cond_cond_eq_cond_inter' hc hfl (measure_ne_top μ _), Set.inter_comm, hmass]
  rfl

/-- The treated arm regression function of the observed outcome is that of `y1`. -/
private lemma cellMean_obs_true' [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (x : 𝒳) : cellMean μ Z X (obs Z y1 y0) true x = cellMean μ Z X y1 true x := by
  have hm : MeasurableSet (armCell Z X true x) :=
    (hZ (measurableSet_singleton true)).inter (hX (measurableSet_singleton x))
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (μ := μ) hm] with ω hω
  have hZω : Z ω = true := hω.1
  simp [obs, hZω]

/-- The control arm regression function of the observed outcome is that of `y0`. -/
private lemma cellMean_obs_false' [IsFiniteMeasure μ] (hZ : Measurable Z) (hX : Measurable X)
    (x : 𝒳) : cellMean μ Z X (obs Z y1 y0) false x = cellMean μ Z X y0 false x := by
  have hm : MeasurableSet (armCell Z X false x) :=
    (hZ (measurableSet_singleton false)).inter (hX (measurableSet_singleton x))
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (μ := μ) hm] with ω hω
  have hZω : Z ω = false := hω.1
  simp [obs, hZω]

/-- `integral_eq_sum_cell` in `cell` notation, for an arbitrary finite measure. -/
private lemma integral_eq_sum_cell' {ν : Measure Ω} [IsFiniteMeasure ν] (hX : Measurable X)
    {f : Ω → ℝ} (hf : Integrable f ν) :
    ∫ ω, f ω ∂ν = ∑ x : 𝒳, (ν (cell X x)).toReal * ∫ ω, f ω ∂(ν[|cell X x]) :=
  integral_eq_sum_cell hX hf

/-- One-sided overlap makes the control arm of a positive cell non-null. -/
private lemma cond_control_ne_zero [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hX : Measurable X) {x : 𝒳} (hcell : μ (cell X x) ≠ 0)
    (hlt : propensity μ Z X x < 1) : (μ[|cell X x]) {ω | Z ω = false} ≠ 0 := by
  intro h
  have hadd := cond_treated_add_cond_control (μ := μ) hX hZ hcell
  have hp : propensity μ Z X x = ((μ[|X ⁻¹' {x}]) {ω | Z ω = true}).toReal := rfl
  have hz : ((μ[|X ⁻¹' {x}]) {ω | Z ω = false}).toReal = 0 := by
    have hzz : (μ[|X ⁻¹' {x}]) {ω | Z ω = false} = 0 := h
    rw [hzz]; simp
  rw [hz, add_zero] at hadd
  rw [hp, hadd] at hlt
  exact lt_irrefl 1 hlt

/-- **The ignorability bridge inside a cell**: under `Y(z) ⫫ Z | X`, the mean of `y` on a
non-null arm of a cell is its unconditional mean in that cell. -/
private lemma integral_arm_eq_of_ignorable [IsProbabilityMeasure μ] {y : Ω → ℝ}
    (hig : Ignorable μ Z y X) (hy : Measurable y) (hZ : Measurable Z) (hX : Measurable X)
    (hi : Integrable y μ) {x : 𝒳} (hcell : μ (cell X x) ≠ 0) {z : Bool}
    (harm : (μ[|cell X x]) {ω | Z ω = z} ≠ 0) :
    ∫ ω, y ω ∂(μ[|armCell Z X z x]) = ∫ ω, y ω ∂(μ[|cell X x]) := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hcell
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hzm : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hcc : (μ[|cell X x])[|{ω | Z ω = z}] = μ[|armCell Z X z x] := by
    rw [cond_cond_eq_cond_inter' hc hzm (measure_ne_top μ _), Set.inter_comm]
    rfl
  rw [← hcc]
  exact integral_cond_arm_eq_of_indepFun (hig x) (integrable_cond' hi) hy hZ harm

/-! ### The theorems -/

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
    Assumption131 μ Z y0 X where
  ignorable := hu.ignorable_right hy1 hy0
  overlap := fun x hcell => (hpos x hcell).2

/-- **Bayes in a covariate cell**: the covariate distribution among the treated reweights
the marginal by the propensity odds, `P(X = x | Z = 1) = P(X = x)·e(x)/e`. -/
theorem cond_cell_given_treated [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hX : Measurable X) (x : 𝒳)
    -- USER-INPUT: some unit is treated; else conditioning on `{Z = 1}` is vacuous
    (hT : μ (treatedEvent Z) ≠ 0) :
    ((μ[|treatedEvent Z]) (cell X x)).toReal
      = (μ (cell X x)).toReal * propensity μ Z X x / (μ (treatedEvent Z)).toReal := by
  have hTm : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  have hLHS : ((μ[|treatedEvent Z]) (cell X x)).toReal
      = (μ (treatedEvent Z)).toReal⁻¹ * (μ (cell X x ∩ treatedEvent Z)).toReal := by
    rw [cond_apply hTm, ENNReal.toReal_mul, ENNReal.toReal_inv, Set.inter_comm]
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · have hz : μ (cell X x ∩ treatedEvent Z) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    rw [hLHS, hz, h0]
    simp
  · have hprop : (μ (cell X x)).toReal * propensity μ Z X x
        = (μ (cell X x ∩ treatedEvent Z)).toReal := by
      rw [propensity, cond_apply hc, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc,
        mul_inv_cancel₀ (by simp [ENNReal.toReal_eq_zero_iff, h0, measure_ne_top μ _]), one_mul]
    rw [hLHS, hprop]
    ring

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
  haveI : IsProbabilityMeasure (μ[|treatedEvent Z]) := cond_isProbabilityMeasure hT
  have hTm : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hobsT : ∫ ω, obs Z y1 y0 ω ∂(μ[|treatedEvent Z])
      = ∫ ω, y1 ω ∂(μ[|treatedEvent Z]) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (μ := μ) hTm] with ω hω
    have hZω : Z ω = true := hω
    simp [obs, hZω]
  have hsplit : att μ Z y1 y0
      = (∫ ω, y1 ω ∂(μ[|treatedEvent Z])) - ∫ ω, y0 ω ∂(μ[|treatedEvent Z]) :=
    integral_sub (integrable_cond' hi1) (integrable_cond' hi0)
  rw [hsplit, hobsT]
  congr 1
  rw [integral_eq_sum_cell' (ν := μ[|treatedEvent Z]) hX (integrable_cond' hi0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  rcases eq_or_ne ((μ[|treatedEvent Z]) (cell X x)) 0 with h | h
  · rw [h]; simp
  · have hTc : μ (treatedEvent Z ∩ cell X x) ≠ 0 := fun hz =>
      h (by rw [cond_apply hTm, hz, mul_zero])
    have hcell : μ (cell X x) ≠ 0 := fun hz =>
      hTc (measure_mono_null Set.inter_subset_right hz)
    have harmT : (μ[|cell X x]) (treatedEvent Z) ≠ 0 := by
      rw [cond_apply hc]
      refine mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top μ _)) ?_
      rw [Set.inter_comm]
      exact hTc
    have hcc : (μ[|treatedEvent Z])[|cell X x] = μ[|armCell Z X true x] := by
      rw [cond_cond_eq_cond_inter' hTm hc (measure_ne_top μ _)]
      rfl
    have hL : ∫ ω, y0 ω ∂(μ[|armCell Z X true x]) = ∫ ω, y0 ω ∂(μ[|cell X x]) :=
      integral_arm_eq_of_ignorable h131.ignorable hy0 hZ hX hi0 hcell harmT
    have hR : cellMean μ Z X (obs Z y1 y0) false x = ∫ ω, y0 ω ∂(μ[|cell X x]) := by
      rw [cellMean_obs_false' hZ hX x]
      exact integral_arm_eq_of_ignorable h131.ignorable hy0 hZ hX hi0 hcell
        (cond_control_ne_zero hZ hX hcell (h131.overlap x hcell))
    rw [hcc, hL, hR]

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
  have hTm : MeasurableSet (treatedEvent Z) := hZ (measurableSet_singleton true)
  have hobs : Integrable (obs Z y1 y0) μ := integrable_obs' hZ hi1 hi0
  have hIC : Integrable (fun ω => (1 - ind (Z ω)) * obs Z y1 y0 ω) μ := by
    rw [one_sub_ind_mul_eq_indicator]
    exact hobs.indicator (hZ (measurableSet_singleton false))
  have hInt : Integrable (fun ω => (propensity μ Z X (X ω) / (μ (treatedEvent Z)).toReal)
      * ((1 - ind (Z ω)) / (1 - propensity μ Z X (X ω))) * obs Z y1 y0 ω) μ := by
    have hrw : (fun ω => (propensity μ Z X (X ω) / (μ (treatedEvent Z)).toReal)
          * ((1 - ind (Z ω)) / (1 - propensity μ Z X (X ω))) * obs Z y1 y0 ω)
        = fun ω => ((propensity μ Z X (X ω) / (μ (treatedEvent Z)).toReal)
            * (1 - propensity μ Z X (X ω))⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω) := by
      funext ω; ring
    rw [hrw]
    exact integrable_comp_mul' hX
      (fun x => (propensity μ Z X x / (μ (treatedEvent Z)).toReal)
        * (1 - propensity μ Z X x)⁻¹) hIC
  rw [att_eq_sub_sum_cellMean h131 hy1 hy0 hZ hX hi1 hi0 hT]
  congr 1
  rw [integral_eq_sum_cell' (ν := μ) hX hInt]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · have hz : μ (treatedEvent Z ∩ cell X x) = 0 :=
      measure_mono_null Set.inter_subset_right h0
    rw [cond_apply hTm, hz, mul_zero]
    simp [h0]
  · have hcongr : ∫ ω, (propensity μ Z X (X ω) / (μ (treatedEvent Z)).toReal)
          * ((1 - ind (Z ω)) / (1 - propensity μ Z X (X ω))) * obs Z y1 y0 ω
          ∂(μ[|cell X x])
        = ∫ ω, ((propensity μ Z X x / (μ (treatedEvent Z)).toReal)
            * (1 - propensity μ Z X x)⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω)
          ∂(μ[|cell X x]) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_cond_mem (μ := μ) hc] with ω hω
      have hXω : X ω = x := hω
      rw [hXω]; ring
    have hcm : ∫ ω, ((propensity μ Z X x / (μ (treatedEvent Z)).toReal)
          * (1 - propensity μ Z X x)⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω) ∂(μ[|cell X x])
        = ((propensity μ Z X x / (μ (treatedEvent Z)).toReal)
            * (1 - propensity μ Z X x)⁻¹)
          * ∫ ω, (1 - ind (Z ω)) * obs Z y1 y0 ω ∂(μ[|cell X x]) := integral_const_mul _ _
    rw [hcongr, hcm, integral_one_sub_ind_mul_cond_cell hZ hX hobs h0,
      cond_cell_given_treated hZ hX x hT]
    have he1 : 1 - propensity μ Z X x ≠ 0 := sub_ne_zero.mpr (h131.overlap x h0).ne'
    field_simp

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
  have hobs : Integrable (obs Z y1 y0) μ := integrable_obs' hZ hi1 hi0
  have hIT : Integrable (fun ω => ind (Z ω) * obs Z y1 y0 ω) μ := by
    rw [ind_mul_eq_indicator]
    exact hobs.indicator (hZ (measurableSet_singleton true))
  have hIC : Integrable (fun ω => (1 - ind (Z ω)) * obs Z y1 y0 ω) μ := by
    rw [one_sub_ind_mul_eq_indicator]
    exact hobs.indicator (hZ (measurableSet_singleton false))
  have hL : Integrable (fun ω => h (X ω) * (y1 ω - y0 ω)) μ :=
    integrable_comp_mul' hX h (hi1.sub hi0)
  have hR1 : Integrable
      (fun ω => ind (Z ω) * h (X ω) * obs Z y1 y0 ω / propensity μ Z X (X ω)) μ := by
    have hrw : (fun ω => ind (Z ω) * h (X ω) * obs Z y1 y0 ω / propensity μ Z X (X ω))
        = fun ω => (h (X ω) * (propensity μ Z X (X ω))⁻¹) * (ind (Z ω) * obs Z y1 y0 ω) := by
      funext ω; ring
    rw [hrw]
    exact integrable_comp_mul' hX (fun x => h x * (propensity μ Z X x)⁻¹) hIT
  have hR0 : Integrable
      (fun ω => (1 - ind (Z ω)) * h (X ω) * obs Z y1 y0 ω
        / (1 - propensity μ Z X (X ω))) μ := by
    have hrw : (fun ω => (1 - ind (Z ω)) * h (X ω) * obs Z y1 y0 ω
          / (1 - propensity μ Z X (X ω)))
        = fun ω => (h (X ω) * (1 - propensity μ Z X (X ω))⁻¹)
            * ((1 - ind (Z ω)) * obs Z y1 y0 ω) := by
      funext ω; ring
    rw [hrw]
    exact integrable_comp_mul' hX (fun x => h x * (1 - propensity μ Z X x)⁻¹) hIC
  have hRsub : Integrable
      (fun ω => ind (Z ω) * h (X ω) * obs Z y1 y0 ω / propensity μ Z X (X ω)
        - (1 - ind (Z ω)) * h (X ω) * obs Z y1 y0 ω / (1 - propensity μ Z X (X ω))) μ :=
    hR1.sub hR0
  rw [weightedATE]
  congr 1
  rw [integral_eq_sum_cell' (ν := μ) hX hL, integral_eq_sum_cell' (ν := μ) hX hRsub]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : MeasurableSet (cell X x) := hX (measurableSet_singleton x)
  rcases eq_or_ne (μ (cell X x)) 0 with h0 | h0
  · simp [h0]
  · have he0 : propensity μ Z X x ≠ 0 := (hpos x h0).1.ne'
    have he1 : 1 - propensity μ Z X x ≠ 0 := sub_ne_zero.mpr (hpos x h0).2.ne'
    have hcongrL : ∫ ω, h (X ω) * (y1 ω - y0 ω) ∂(μ[|cell X x])
        = ∫ ω, h x * (y1 ω - y0 ω) ∂(μ[|cell X x]) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_cond_mem (μ := μ) hc] with ω hω
      have hXω : X ω = x := hω
      rw [hXω]
    have hcmL : ∫ ω, h x * (y1 ω - y0 ω) ∂(μ[|cell X x])
        = h x * ∫ ω, (y1 ω - y0 ω) ∂(μ[|cell X x]) := integral_const_mul _ _
    have hcongrR : ∫ ω, (ind (Z ω) * h (X ω) * obs Z y1 y0 ω / propensity μ Z X (X ω)
            - (1 - ind (Z ω)) * h (X ω) * obs Z y1 y0 ω / (1 - propensity μ Z X (X ω)))
          ∂(μ[|cell X x])
        = ∫ ω, ((h x * (propensity μ Z X x)⁻¹) * (ind (Z ω) * obs Z y1 y0 ω)
            - (h x * (1 - propensity μ Z X x)⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω))
          ∂(μ[|cell X x]) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_cond_mem (μ := μ) hc] with ω hω
      have hXω : X ω = x := hω
      rw [hXω]; ring
    have hsubR : ∫ ω, ((h x * (propensity μ Z X x)⁻¹) * (ind (Z ω) * obs Z y1 y0 ω)
            - (h x * (1 - propensity μ Z X x)⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω))
          ∂(μ[|cell X x])
        = (∫ ω, (h x * (propensity μ Z X x)⁻¹) * (ind (Z ω) * obs Z y1 y0 ω)
              ∂(μ[|cell X x]))
          - ∫ ω, (h x * (1 - propensity μ Z X x)⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω)
              ∂(μ[|cell X x]) :=
      integral_sub ((integrable_cond' hIT).const_mul _) ((integrable_cond' hIC).const_mul _)
    have hcm1 : ∫ ω, (h x * (propensity μ Z X x)⁻¹) * (ind (Z ω) * obs Z y1 y0 ω)
          ∂(μ[|cell X x])
        = (h x * (propensity μ Z X x)⁻¹)
          * ∫ ω, ind (Z ω) * obs Z y1 y0 ω ∂(μ[|cell X x]) := integral_const_mul _ _
    have hcm0 : ∫ ω, (h x * (1 - propensity μ Z X x)⁻¹) * ((1 - ind (Z ω)) * obs Z y1 y0 ω)
          ∂(μ[|cell X x])
        = (h x * (1 - propensity μ Z X x)⁻¹)
          * ∫ ω, (1 - ind (Z ω)) * obs Z y1 y0 ω ∂(μ[|cell X x]) := integral_const_mul _ _
    have hcate : ∫ ω, (y1 ω - y0 ω) ∂(μ[|cell X x])
        = cellMean μ Z X (obs Z y1 y0) true x - cellMean μ Z X (obs Z y1 y0) false x :=
      cate_eq_cellMean_sub hu hpos hy1 hy0 hZ hX hi1 hi0 h0
    rw [hcongrL, hcmL, hcate, hcongrR, hsubR, hcm1, hcm0,
      integral_ind_mul_cond_cell hZ hX hobs x,
      integral_one_sub_ind_mul_cond_cell hZ hX hobs h0]
    field_simp

/-- **The weight `h ≡ 1` gives the average causal effect** (Ding Theorem 13.4, first table
row). -/
theorem weightedATE_one [IsProbabilityMeasure μ]
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ) :
    weightedATE μ X y1 y0 (fun _ => 1) = ate μ y1 y0 := by
  rw [weightedATE, ate]
  simp

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
