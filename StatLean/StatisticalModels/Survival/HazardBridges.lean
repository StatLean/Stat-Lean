import StatLean.StatisticalModels.Survival.CumulativeHazard
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Classical hazard bridges: `Λ = −log S` and the discrete product formula

The two regime-specific bridges between the cumulative-hazard measure and the survival
function (the fully general mixed-case bridge is the product integral — deliberately
deferred, see below):

* **Continuous bridge (S4.1).** For an atomless event-time law, on the region where survival
  is positive, $\Lambda(0, t] = -\log S(t)$, equivalently $S(t) = e^{-\Lambda(0,t]}$ — the
  identity every parametric survival model is built on.
* **Probability integral transform (`map_cdf_of_noAtoms`)** — the reusable brick behind
  Route A: an atomless law pushed through its own CDF is uniform on `(0, 1]`.
* **Discrete bridge (S4.2).** For a law supported (below `t`) on finitely many atoms,
  $S(t) = \prod_{s \le t} (1 - \Delta\Lambda(s))$ — the population product-limit identity
  mirrored by the Kaplan–Meier estimator.

**Deferred (named debt D-S1):** the mixed-case bridge via the product integral
$S(t) = \prodi_{(0,t]} (1 - \Lambda(ds))$ requires genuine product-integration theory
(R. D. Gill and S. Johansen, "A survey of product-integration with a view toward application
in survival analysis," *Ann. Statist.* **18** (1990), 1501–1555) — a future milestone; the
two regime bridges here cover the textbook uses.

**Reference.** ABGK §II.1 (the `Λ = −log S` identity in the continuous case; the discrete
hazard product) (verify §); J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis
of Failure Time Data*, 2nd ed., Wiley, 2002, §1.2 (verify §). PIT: classical.

**Proof formalization notes.** Route A for S4.1: transport the hazard integral through the
CDF (the PIT brick) to the explicit 1-D integral `∫ (1−u)⁻¹ du = −log(1−·)` (FTC on
`[0, F t]`, `F t < 1` from positive survival). Route B fallback: compare the Stieltjes
measures of `−log S` and `Λ` on `Ioc`-generators. The discrete bridge is a sorted induction
over the atoms with the S-B1 atom formula `ΔΛ = ΔF/S(−)` per step. Sub-probability
generalizations are a later pass (D-S5).

**Bibliographic comments.** `S = e^{−Λ}` in the continuous case is classical actuarial
mathematics; its measure-hazard formulation and the warning that it FAILS with atoms
(whence the product integral) is emphasized by Gill–Johansen (1990) and ABGK §II.6.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

open ProbabilityTheory in
/-- Left-continuity of the CDF of an atomless law: the left limit is the value. -/
private lemma leftLim_cdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] (a : ℝ) :
    Function.leftLim (cdf μ) a = cdf μ a := by
  have h := (cdf μ).measure_singleton a
  rw [measure_cdf μ, MeasureTheory.measure_singleton] at h
  have h1 : cdf μ a - Function.leftLim (cdf μ) a ≤ 0 := ENNReal.ofReal_eq_zero.1 h.symm
  have h2 : Function.leftLim (cdf μ) a ≤ cdf μ a := (monotone_cdf μ).leftLim_le le_rfl
  linarith

/-- **Probability integral transform** (reusable brick): an atomless probability law on ℝ
pushed through its own CDF is uniform on `(0, 1]`. -/
theorem map_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (fun t => ProbabilityTheory.cdf μ t) = volume.restrict (Ioc (0 : ℝ) 1) := by
  have hmono := ProbabilityTheory.monotone_cdf μ
  have hmeas : Measurable (fun t => ProbabilityTheory.cdf μ t) := hmono.measurable
  haveI : IsProbabilityMeasure (μ.map (fun t => ProbabilityTheory.cdf μ t)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_Iic _ _ fun u => ?_
  have hRHS : (volume.restrict (Ioc (0 : ℝ) 1)) (Iic u) = ENNReal.ofReal (min u 1) := by
    rw [Measure.restrict_apply measurableSet_Iic]
    have hset : Iic u ∩ Ioc (0 : ℝ) 1 = Ioc 0 (min u 1) := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
      tauto
    rw [hset, Real.volume_Ioc, sub_zero]
  rw [hRHS, Measure.map_apply hmeas measurableSet_Iic]
  set A : Set ℝ := (fun t => ProbabilityTheory.cdf μ t) ⁻¹' Iic u with hAdef
  have hmemA : ∀ x, x ∈ A ↔ ProbabilityTheory.cdf μ x ≤ u := fun _ => Iff.rfl
  rcases le_or_gt 1 u with hu1 | hu1
  · have hAu : A = univ :=
      eq_univ_of_forall fun x => (hmemA x).2 ((ProbabilityTheory.cdf_le_one μ x).trans hu1)
    rw [hAu, measure_univ, min_eq_right hu1, ENNReal.ofReal_one]
  rcases lt_or_ge u 0 with hu0 | hu0
  · have hAe : A = ∅ :=
      eq_empty_of_forall_notMem fun x hx =>
        absurd ((hmemA x).1 hx) (not_le.2 (hu0.trans_le (ProbabilityTheory.cdf_nonneg μ x)))
    rw [hAe, measure_empty, min_eq_left hu1.le, ENNReal.ofReal_eq_zero.2 hu0.le]
  rw [min_eq_left hu1.le]
  rcases eq_empty_or_nonempty A with hAe | hAne
  · have hu' : u ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨x, hx⟩ :=
        ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hcon)).exists
      have hxA : x ∈ A := (hmemA x).2 hx.le
      rw [hAe] at hxA
      exact hxA
    rw [hAe, measure_empty, le_antisymm hu' hu0, ENNReal.ofReal_zero]
  obtain ⟨x₀, hx₀⟩ :=
    ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hu1)).exists
  have hbdd : BddAbove A := by
    refine ⟨x₀, fun x hx => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact absurd ((hmemA x).1 hx) (not_le.2 (hx₀.trans_le (hmono hcon.le)))
  set a := sSup A with hadef
  have hIio : Iio a ⊆ A := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup hAne hx
    exact (hmemA x).2 ((hmono hxy.le).trans ((hmemA y).1 hy))
  have hAmeas : μ A = μ (Iic a) := by
    refine le_antisymm (measure_mono fun x hx => le_csSup hbdd hx) ?_
    calc μ (Iic a) = μ (Iio a) := (measure_congr Iio_ae_eq_Iic).symm
      _ ≤ μ A := measure_mono hIio
  have hcdfa : ProbabilityTheory.cdf μ a = u := by
    refine le_antisymm ?_ ?_
    · rw [← leftLim_cdf_eq μ a]
      refine le_of_tendsto (hmono.tendsto_leftLim a) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx using (hmemA x).1 (hIio hx)
    · refine ge_of_tendsto (((ProbabilityTheory.cdf μ).right_continuous a).mono
        Ioi_subset_Ici_self) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      by_contra hcon
      push_neg at hcon
      exact absurd (le_csSup hbdd ((hmemA x).2 hcon.le)) (not_le.2 hx)
  rw [hAmeas, ← ProbabilityTheory.ofReal_cdf μ a, hcdfa]

open ProbabilityTheory in
/-- A CDF level set is null for the law itself (immediate from the PIT). -/
private lemma measure_preimage_cdf_singleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NoAtoms μ] (c : ℝ) : μ ((fun x => cdf μ x) ⁻¹' {c}) = 0 := by
  have hmeas : Measurable (fun x => cdf μ x) := (monotone_cdf μ).measurable
  rw [← Measure.map_apply hmeas (measurableSet_singleton c), map_cdf_of_noAtoms μ,
    Measure.restrict_apply (measurableSet_singleton c)]
  exact measure_mono_null inter_subset_left (measure_singleton c)

/-- The explicit one-dimensional hazard integral `∫₀^c (1 − u)⁻¹ du = −log (1 − c)`. -/
private lemma lintegral_inv_one_sub {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∫⁻ u in Ioc (0 : ℝ) c, (ENNReal.ofReal (1 - u))⁻¹ = ENNReal.ofReal (-Real.log (1 - c)) := by
  have hpos : ∀ u ∈ Icc (0 : ℝ) c, (0 : ℝ) < 1 - u := by
    intro u hu
    have := hu.2
    linarith
  have hcont : ContinuousOn (fun u : ℝ => (1 - u)⁻¹) (Icc 0 c) :=
    ContinuousOn.inv₀ ((continuous_const.sub continuous_id).continuousOn)
      fun u hu => ne_of_gt (hpos u hu)
  have hint : IntegrableOn (fun u : ℝ => (1 - u)⁻¹) (Ioc 0 c) volume :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) c)] fun u : ℝ => (1 - u)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact le_of_lt (inv_pos.2 (hpos u ⟨hu.1.le, hu.2⟩))
  have hIeq : ∫⁻ u in Ioc (0 : ℝ) c, (ENNReal.ofReal (1 - u))⁻¹
      = ∫⁻ u in Ioc (0 : ℝ) c, ENNReal.ofReal ((1 - u)⁻¹) :=
    setLIntegral_congr_fun measurableSet_Ioc fun u hu =>
      (ENNReal.ofReal_inv_of_pos (hpos u ⟨hu.1.le, hu.2⟩)).symm
  rw [hIeq, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hc0]
  have hcont' : ContinuousOn (fun u : ℝ => (1 - u)⁻¹) (uIcc 0 c) := by
    rwa [uIcc_of_le hc0]
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) c,
      HasDerivAt (fun y : ℝ => -Real.log (1 - y)) ((1 - u)⁻¹) u := by
    intro u hu
    rw [uIcc_of_le hc0] at hu
    have hne : (1 : ℝ) - u ≠ 0 := ne_of_gt (hpos u hu)
    have hd : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 1
    simpa using ((Real.hasDerivAt_log hne).comp u hd).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable]
  simp

/-- **S4.1, continuous bridge**: for an atomless event-time law, where survival is positive,
`Λ(0, t] = −log S(t)` (ABGK §II.1; Kalbfleisch–Prentice §1.2). -/
theorem cumHazard_Ioc_eq_neg_log (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ)
    -- USER-INPUT: continuous (atomless) law — the identity FAILS with atoms; ABGK §II.6
    [NoAtoms μ] {t : ℝ}
    -- USER-INPUT: inside the support (positive survival); ABGK §II.1
    (ht : survival μ t ≠ 0) :
    (cumHazard μ (Ioc 0 t)).toReal = -Real.log (survivalReal μ t) := by
  sorry

/-- **S4.1', exponential form**: `S(t) = e^{−Λ(0,t]}` under the same hypotheses. -/
theorem survivalReal_eq_exp_neg_cumHazard (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ)
    -- USER-INPUT: atomless; ABGK §II.6
    [NoAtoms μ] {t : ℝ}
    -- USER-INPUT: positive survival; ABGK §II.1
    (ht : survival μ t ≠ 0) :
    survivalReal μ t = Real.exp (-(cumHazard μ (Ioc 0 t)).toReal) := by
  haveI := hev.1
  have hpos : 0 < survivalReal μ t :=
    ENNReal.toReal_pos ht (measure_ne_top _ _)
  rw [cumHazard_Ioc_eq_neg_log μ hev ht, neg_neg, Real.exp_log hpos]

/-- The cumulative hazard of an atomless law is finite up to any time with positive
survival (the `toReal` in S4.1 is honest). -/
theorem cumHazard_Ioc_lt_top (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ)
    -- USER-INPUT: atomless; ABGK §II.6
    [NoAtoms μ] {t : ℝ}
    -- USER-INPUT: positive survival; ABGK §II.1
    (ht : survival μ t ≠ 0) :
    cumHazard μ (Ioc 0 t) < ⊤ := by
  haveI := hev.1
  have hIci : μ (Ici t) ≠ 0 := fun h => ht (measure_mono_null Ioi_subset_Ici_self h)
  calc cumHazard μ (Ioc 0 t) ≤ cumHazard μ (Iic t) := measure_mono Ioc_subset_Iic_self
    _ ≤ (μ (Ici t))⁻¹ := cumHazard_Iic_le μ t
    _ < ⊤ := ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hIci)

/-- **S4.2, discrete bridge**: for an event-time law whose mass below `t` sits on the finite
set `E`, the survival function is the product of one-minus-hazard-jumps —
`S(t) = ∏_{s ∈ E, s ≤ t} (1 − ΔΛ(s))` (ABGK §II.1 discrete case; the population identity
behind Kaplan–Meier). -/
theorem survivalReal_eq_prod_one_sub_jump (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ) (E : Finset ℝ) {t : ℝ}
    -- USER-INPUT: finitely supported below t — all mass in `Iic t` sits on E; ABGK §II.1
    (hsupp : μ (Iic t \ (E.filter (· ≤ t) : Finset ℝ)) = 0) :
    survivalReal μ t = ∏ s ∈ E.filter (· ≤ t), (1 - (cumHazardJump μ s).toReal) := by
  sorry

end StatLean.StatisticalModels.Survival
