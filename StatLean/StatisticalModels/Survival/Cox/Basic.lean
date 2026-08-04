import StatLean.StatisticalModels.Survival.Cox.Defs
import StatLean.StatisticalModels.Survival.CumulativeHazard

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
  have htop : Tendsto (coxSF β Λ₀ z hfin) atTop (𝓝 1) := by
    simpa using hS.const_sub (1 : ℝ)
  refine ⟨⟨?_⟩, coxMeasure_Iio_zero β Λ₀ z hfin⟩
  rw [coxMeasure, (coxSF β Λ₀ z hfin).measure_univ (tendsto_coxSF_atBot β Λ₀ z hfin) htop]
  simp

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
