import StatLean.StatisticalModels.Survival.Cox.Defs
import StatLean.StatisticalModels.Survival.HazardBridges

/-!
# The canonical Cox law — construction and realization

The construction side of the Cox model: for a continuous, locally finite baseline `Λ₀`
concentrated on `(0, ∞)`, the survival function `coxSurvival β Λ₀ z` is a genuine
(sub-)survival curve; its Stieltjes law `coxMeasure β Λ₀ z` is an event-time law exactly when
the total baseline hazard is infinite (else the defect is the cure mass); and — the
realization theorem **S5.2** — the constructed family has exactly the proportional-hazards
structure it was built from: `cumHazard (coxMeasure β Λ₀ z) = e^{⟪β,z⟫} • Λ₀`.

S5.2 is this batch's designated hard theorem (it rides the S-B4 analytic bricks); it is the
single allowed carry if the bridge batch slips.

**Reference.** `Cox72 §2`; ABGK §III.1.2 (verify §): the multiplicative-hazard model and its
absolutely-continuous construction.

**Proof formalization notes.** Monotonicity/right-continuity of `1 − coxSurvival` come from
monotonicity and continuity-from-above of `Λ₀(Ioc 0 ·]` (no atoms ⇒ continuity, whence the
Stieltjes packaging); probability-vs-defect is the `t → ∞` limit against
`Tendsto (Λ₀ (Ioc 0 ·)) atTop (𝓝 ⊤)`. S5.2 reduces, per evaluation set, to the
scalar Stieltjes-FTC identity `∫_{(a,b]} c·e^{−c·G(t)} dΛ₀(t) = e^{−c·G(a)} − e^{−c·G(b)}`
with `G t = Λ₀(Ioc 0 t]` — shared machinery with `HazardBridges` (S4.1's Route A/B bricks).

**Bibliographic comments.** The exponential-of-integrated-hazard construction is classical
(actuarial); Cox (1972) §2 uses it implicitly; ABGK III.1.2 states it in measure form.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.Survival

variable {p : ℕ}

/-- The real-valued baseline cumulative hazard `t ↦ Λ₀(0, t]` is monotone. -/
private theorem monotone_baselineToReal (Λ₀ : Measure ℝ) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) :
    Monotone fun t => (Λ₀ (Ioc 0 t)).toReal := fun _ _ hst =>
  ENNReal.toReal_mono (hfin _) (measure_mono (Ioc_subset_Ioc_right hst))

/-- Below the origin the baseline cumulative hazard vanishes (`Ioc 0 t = ∅`). -/
private theorem baselineToReal_of_nonpos (Λ₀ : Measure ℝ) {t : ℝ} (ht : t ≤ 0) :
    (Λ₀ (Ioc 0 t)).toReal = 0 := by
  rw [Ioc_eq_empty (by simpa using ht)]
  simp

/-- The Cox survival function is antitone (given a locally finite baseline). -/
theorem antitone_coxSurvival (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: locally finite baseline hazard (Λ₀(0,t] < ∞); Cox72 §2
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) :
    Antitone (coxSurvival β Λ₀ z) := by
  intro s t hst
  refine Real.exp_le_exp.mpr ?_
  have hG : (Λ₀ (Ioc 0 s)).toReal ≤ (Λ₀ (Ioc 0 t)).toReal :=
    monotone_baselineToReal Λ₀ hfin hst
  have hc : (0 : ℝ) < Real.exp ⟪β, z⟫_ℝ := Real.exp_pos _
  nlinarith

/-- The Cox survival function takes values in `(0, 1]` for finite baseline hazard. -/
theorem coxSurvival_mem_Ioc (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: locally finite baseline; Cox72 §2
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) (t : ℝ) :
    coxSurvival β Λ₀ z t ∈ Ioc (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [coxSurvival, Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

/-- The **canonical Cox law**: the Stieltjes measure of `1 − coxSurvival` (`Cox72 §2`).
Packaged as a sorried Stieltjes construction with its spec lemma; the closure builds the
monotone/right-continuous structure from `antitone_coxSurvival` + continuity of `Λ₀`. -/
noncomputable def coxSF (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    StieltjesFunction ℝ where
  toFun t := 1 - coxSurvival β Λ₀ z t
  mono' _ _ hst := by
    have := antitone_coxSurvival β Λ₀ z hfin hst
    dsimp only
    linarith
  right_continuous' x := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    -- continuity from above of `r ↦ Λ₀ (0, r]` at `x`, then compose with `1 - exp(-c·)`
    have hIoc : ⋂ r > x, Ioc (0 : ℝ) r = Ioc 0 x := by
      refine Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
      · simp only [mem_iInter, mem_Ioc] at hy
        have h0 := (hy (x + 1) (by linarith)).1
        refine ⟨h0, le_of_forall_gt_imp_ge_of_dense fun r hr => (hy r ?_).2⟩
        exact lt_of_le_of_lt le_rfl hr
      · simp only [mem_iInter, mem_Ioc]
        exact fun r hr => ⟨hy.1, hy.2.trans hr.le⟩
    have hmeas : Tendsto (fun r => Λ₀ (Ioc 0 r)) (𝓝[Ioi x] x) (𝓝 (Λ₀ (Ioc 0 x))) := by
      have h := tendsto_measure_biInter_gt (μ := Λ₀) (s := fun r : ℝ => Ioc (0 : ℝ) r) (a := x)
        (fun r _ => measurableSet_Ioc.nullMeasurableSet)
        (fun _ _ _ hij => Ioc_subset_Ioc_right hij) ⟨x + 1, by linarith, hfin _⟩
      rwa [hIoc] at h
    have hreal : Tendsto (fun r => (Λ₀ (Ioc 0 r)).toReal) (𝓝[Ioi x] x)
        (𝓝 ((Λ₀ (Ioc 0 x)).toReal)) := (ENNReal.tendsto_toReal (hfin x)).comp hmeas
    exact (((hreal.const_mul (Real.exp ⟪β, z⟫_ℝ)).neg).rexp).const_sub 1

@[simp]
theorem coxSF_apply (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] (t : ℝ) :
    coxSF β Λ₀ z hfin t = 1 - coxSurvival β Λ₀ z t := rfl

/-- The canonical Cox event-time law. -/
noncomputable def coxMeasure (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    Measure ℝ :=
  (coxSF β Λ₀ z hfin).measure

/-- `coxSF` vanishes identically on the non-positive axis, hence tends to `0` at `-∞`. -/
private theorem tendsto_coxSF_atBot (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    Tendsto (coxSF β Λ₀ z hfin) atBot (𝓝 0) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  rw [coxSF_apply, coxSurvival, baselineToReal_of_nonpos Λ₀ ht]
  simp

/-- The Cox law puts no mass strictly below the origin. -/
private theorem coxMeasure_Iio_zero (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    coxMeasure β Λ₀ z hfin (Iio 0) = 0 := by
  have hle : coxMeasure β Λ₀ z hfin (Iio 0) ≤ (coxSF β Λ₀ z hfin).measure (Iic 0) :=
    measure_mono Iio_subset_Iic_self
  rw [(coxSF β Λ₀ z hfin).measure_Iic (tendsto_coxSF_atBot β Λ₀ z hfin) 0] at hle
  have h0 : coxSF β Λ₀ z hfin 0 = 0 := by
    rw [coxSF_apply, coxSurvival, baselineToReal_of_nonpos Λ₀ le_rfl]; simp
  rw [h0] at hle
  simpa using hle

/-- Left-continuity of the baseline cumulative hazard, along `x − 1/(n+1)`: an atomless
baseline puts no mass on `{x}`, so `Λ₀(0, ·]` has no jump there. -/
private theorem tendsto_baselineMeasure_left (Λ₀ : Measure ℝ) [NoAtoms Λ₀] (x : ℝ) :
    Tendsto (fun n : ℕ => Λ₀ (Ioc 0 (x - 1 / (n + 1)))) atTop (𝓝 (Λ₀ (Ioc 0 x))) := by
  have hmono : Monotone fun n : ℕ => Ioc (0 : ℝ) (x - 1 / (n + 1)) := by
    intro m n hmn
    refine Ioc_subset_Ioc_right ?_
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hmn' : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    have hinv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le hm hmn'
    linarith
  have hunion : (⋃ n : ℕ, Ioc (0 : ℝ) (x - 1 / (n + 1))) = Ioo 0 x := by
    ext y
    simp only [mem_iUnion, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨n, hy0, hyn⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨hy0, by linarith⟩
    · rintro ⟨hy0, hyx⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - y by linarith)
      exact ⟨n, hy0, by linarith⟩
  have h := tendsto_measure_iUnion_atTop (μ := Λ₀) hmono
  rw [hunion, measure_congr (Ioo_ae_eq_Ioc (μ := Λ₀) (a := 0) (b := x))] at h
  exact h

/-- The Cox distribution function is left-continuous: its left limit is its value. -/
private theorem leftLim_coxSF (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] (x : ℝ) :
    Function.leftLim (coxSF β Λ₀ z hfin) x = coxSF β Λ₀ z hfin x := by
  have hG : Tendsto (fun n : ℕ => (Λ₀ (Ioc 0 (x - 1 / (n + 1)))).toReal) atTop
      (𝓝 ((Λ₀ (Ioc 0 x)).toReal)) :=
    (ENNReal.tendsto_toReal (hfin x)).comp (tendsto_baselineMeasure_left Λ₀ x)
  have hf : Tendsto (fun n : ℕ => coxSF β Λ₀ z hfin (x - 1 / (n + 1))) atTop
      (𝓝 (coxSF β Λ₀ z hfin x)) := by
    simp only [coxSF_apply, coxSurvival]
    exact (((hG.const_mul (Real.exp ⟪β, z⟫_ℝ)).neg).rexp).const_sub 1
  refine le_antisymm ((coxSF β Λ₀ z hfin).mono'.leftLim_le le_rfl) ?_
  refine le_of_tendsto hf (Filter.Eventually.of_forall fun n => ?_)
  refine (coxSF β Λ₀ z hfin).mono'.le_leftLim ?_
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- The canonical Cox law is atomless (its distribution function is left-continuous). -/
private theorem coxMeasure_singleton (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] (x : ℝ) :
    coxMeasure β Λ₀ z hfin {x} = 0 := by
  rw [coxMeasure, (coxSF β Λ₀ z hfin).measure_singleton x, leftLim_coxSF, sub_self,
    ENNReal.ofReal_zero]

/-- Under a diverging total baseline hazard the Cox distribution function increases to one. -/
private theorem tendsto_coxSF_atTop (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p)) (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀]
    (htot : Tendsto (fun t => Λ₀ (Ioc 0 t)) atTop (𝓝 ⊤)) :
    Tendsto (coxSF β Λ₀ z hfin) atTop (𝓝 1) := by
  -- the real-valued baseline hazard diverges, so the survival function collapses to `0`
  have hG : Tendsto (fun t => (Λ₀ (Ioc 0 t)).toReal) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [ENNReal.tendsto_nhds_top_iff_nnreal.1 htot b.toNNReal] with t ht
    have h2 : ((b.toNNReal : ℝ≥0∞)).toReal ≤ (Λ₀ (Ioc 0 t)).toReal :=
      (ENNReal.toReal_le_toReal (by simp) (hfin t)).2 ht.le
    simp only [ENNReal.coe_toReal, Real.coe_toNNReal'] at h2
    exact (le_max_left b 0).trans h2
  have hS : Tendsto (coxSurvival β Λ₀ z) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop (Real.exp_pos _) hG))
  simpa using hS.const_sub (1 : ℝ)

/-- The Cox law is a (possibly defective) event-time law: mass on `[0, ∞)`, total at most
one; it is a probability law **iff** the total baseline hazard diverges (else the defect is
the cure fraction — documented, ABGK §II.1 defective case). -/
theorem isSubEventTimeLaw_coxMeasure (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    IsSubEventTimeLaw (coxMeasure β Λ₀ z hfin) := by
  refine ⟨?_, coxMeasure_Iio_zero β Λ₀ z hfin⟩
  have hle : ∀ t, coxSF β Λ₀ z hfin t ≤ 1 := fun t => by
    rw [coxSF_apply]
    have := (coxSurvival_mem_Ioc β Λ₀ z hfin t).1
    linarith
  have hbdd : BddAbove (Set.range (coxSF β Λ₀ z hfin)) := ⟨1, by rintro y ⟨t, rfl⟩; exact hle t⟩
  have htop := tendsto_atTop_ciSup (coxSF β Λ₀ z hfin).mono hbdd
  rw [coxMeasure, (coxSF β Λ₀ z hfin).measure_univ (tendsto_coxSF_atBot β Λ₀ z hfin) htop]
  refine ENNReal.ofReal_le_one.2 ?_
  have : ⨆ t, coxSF β Λ₀ z hfin t ≤ 1 := ciSup_le hle
  linarith

/-- Probability (no cure) under diverging total baseline hazard. -/
theorem isEventTimeLaw_coxMeasure (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀]
    -- USER-INPUT: infinite total baseline hazard (no cure mass); ABGK §II.1
    (htot : Tendsto (fun t => Λ₀ (Ioc 0 t)) atTop (𝓝 ⊤)) :
    IsEventTimeLaw (coxMeasure β Λ₀ z hfin) := by
  refine ⟨⟨?_⟩, coxMeasure_Iio_zero β Λ₀ z hfin⟩
  rw [coxMeasure, (coxSF β Λ₀ z hfin).measure_univ (tendsto_coxSF_atBot β Λ₀ z hfin)
    (tendsto_coxSF_atTop β Λ₀ z hfin htot)]
  simp

/-- **S5.2 in the no-cure regime** (`Cox72 §2`; ABGK §III.1.2): when the total baseline
hazard diverges, the constructed Cox law is a genuine atomless event-time law and its
cumulative-hazard measure is exactly `e^{⟪β,z⟫} • Λ₀`. This is the realization theorem in
the regime where it holds; see the falsity note on `cumHazard_coxMeasure` below for why the
divergence hypothesis cannot be dropped.

The analytic content is the `Λ = −log S` bridge S4.1 (`HazardBridges`): the constructed law
has survival `e^{−e^{⟪β,z⟫} Λ₀(0,t]}`, so `Λ(0,t] = e^{⟪β,z⟫} Λ₀(0,t]` for every `t`, and
both measures vanish on `(−∞, 0]`; a `Iic`-difference then upgrades this to all of `Ioc`. -/
theorem cumHazard_coxMeasure_of_tendsto_top (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀]
    -- USER-INPUT: infinite total baseline hazard (no cure mass); ABGK §II.1
    (htot : Tendsto (fun t => Λ₀ (Ioc 0 t)) atTop (𝓝 ⊤)) :
    cumHazard (coxMeasure β Λ₀ z hfin) = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀ := by
  haveI : NoAtoms (coxMeasure β Λ₀ z hfin) := ⟨coxMeasure_singleton β Λ₀ z hfin⟩
  have hev : IsEventTimeLaw (coxMeasure β Λ₀ z hfin) :=
    isEventTimeLaw_coxMeasure β Λ₀ z hΛ0 hfin htot
  haveI := hev.1
  -- the survival function of the constructed law is the Cox survival function
  have hsurv : ∀ t, survivalReal (coxMeasure β Λ₀ z hfin) t = coxSurvival β Λ₀ z t := by
    intro t
    rw [survivalReal, survival, coxMeasure,
      (coxSF β Λ₀ z hfin).measure_Ioi (tendsto_coxSF_atTop β Λ₀ z hfin htot) t, coxSF_apply,
      sub_sub_cancel, ENNReal.toReal_ofReal (coxSurvival_mem_Ioc β Λ₀ z hfin t).1.le]
  have hne : ∀ t, survival (coxMeasure β Λ₀ z hfin) t ≠ 0 := by
    intro t h
    have h0 : survivalReal (coxMeasure β Λ₀ z hfin) t = 0 := by
      rw [survivalReal, h, ENNReal.toReal_zero]
    rw [hsurv t] at h0
    exact absurd h0 (Real.exp_ne_zero _)
  -- S4.1 evaluates the cumulative hazard up to any time
  have hIoc : ∀ t, cumHazard (coxMeasure β Λ₀ z hfin) (Ioc 0 t)
      = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) * Λ₀ (Ioc 0 t) := by
    intro t
    have h1 := cumHazard_Ioc_eq_neg_log (coxMeasure β Λ₀ z hfin) hev (hne t)
    rw [hsurv t, coxSurvival, Real.log_exp, neg_neg] at h1
    have h2 : cumHazard (coxMeasure β Λ₀ z hfin) (Ioc 0 t) ≠ ⊤ :=
      (cumHazard_Ioc_lt_top (coxMeasure β Λ₀ z hfin) hev (hne t)).ne
    rw [← ENNReal.ofReal_toReal h2, h1, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_toReal (hfin t)]
  -- both sides vanish on the non-positive axis, so `Iic` reduces to `Ioc 0 ·`
  have hcum0 : cumHazard (coxMeasure β Λ₀ z hfin) (Iic 0) = 0 := by
    rw [cumHazard_apply _ measurableSet_Iic]
    refine setLIntegral_measure_zero _ _ ?_
    rw [← Iio_union_right]
    exact measure_union_null hev.2 (measure_singleton 0)
  have hIicC : ∀ t, cumHazard (coxMeasure β Λ₀ z hfin) (Iic t)
      = cumHazard (coxMeasure β Λ₀ z hfin) (Ioc 0 t) := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · rw [Ioc_eq_empty (not_lt.2 ht), measure_empty]
      exact measure_mono_null (Iic_subset_Iic.2 ht) hcum0
    · rw [← Iic_union_Ioc_eq_Iic ht.le,
        measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, hcum0, zero_add]
  have hIicB : ∀ t, Λ₀ (Iic t) = Λ₀ (Ioc 0 t) := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · rw [Ioc_eq_empty (not_lt.2 ht), measure_empty]
      exact measure_mono_null (Iic_subset_Iic.2 ht) hΛ0
    · rw [← Iic_union_Ioc_eq_Iic ht.le,
        measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, hΛ0, zero_add]
  have hkey : ∀ t, cumHazard (coxMeasure β Λ₀ z hfin) (Iic t)
      = (ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀) (Iic t) := by
    intro t
    rw [Measure.smul_apply, smul_eq_mul, hIicC t, hIoc t, hIicB t]
  have hfinC : ∀ t, cumHazard (coxMeasure β Λ₀ z hfin) (Iic t) ≠ ⊤ := by
    intro t
    rw [hIicC t, hIoc t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin t)
  have hfinB : ∀ t, (ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀) (Iic t) ≠ ⊤ := fun t => by
    rw [← hkey t]; exact hfinC t
  have hdiff : ∀ a b : ℝ, Iic b \ Iic a = Ioc a b := by
    intro a b
    ext x
    simp only [mem_diff, mem_Iic, mem_Ioc, not_le]
    exact and_comm
  refine Measure.ext_of_Ioc' _ _ (fun a b hab => ?_) (fun a b hab => ?_)
  · rw [← hdiff a b, measure_diff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (hfinC a)]
    exact ne_top_of_le_ne_top (hfinC b) tsub_le_self
  · rw [← hdiff a b,
      measure_diff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (hfinC a),
      measure_diff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (hfinB a),
      hkey a, hkey b]

/-- **S5.2, the realization theorem** (`Cox72 §2`; ABGK §III.1.2): the constructed Cox law
has exactly the proportional-hazards structure — its cumulative-hazard measure is
`e^{⟪β,z⟫} • Λ₀` (restricted to the positive axis carrying the baseline). Designated hard
theorem of this batch (rides the S-B4 bricks; the single allowed carry). -/
theorem cumHazard_coxMeasure (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
    (z : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    cumHazard (coxMeasure β Λ₀ z hfin) = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀ := by
  -- TODO (S5.2, designated carry): rides the S-B4 analytic bricks of
  -- `Survival.HazardBridges`, which are not on this branch yet. Per evaluation set the
  -- goal reduces to the Stieltjes-FTC identity
  -- `∫_{(a,b]} c·e^{−c·G t} dΛ₀ t = e^{−c·G a} − e^{−c·G b}` with `G t = Λ₀ (Ioc 0 t)`.
  sorry

end StatLean.StatisticalModels.Survival
