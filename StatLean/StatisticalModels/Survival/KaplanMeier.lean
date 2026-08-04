import StatLean.StatisticalModels.Survival.CumulativeHazard

/-!
# Kaplan–Meier and Nelson–Aalen — the finite-sample product-limit layer

The nonparametric estimators on right-censored data `d : Fin n → ℝ × Bool` (observed time,
event indicator):

* `atRisk d t` — the size of the risk set `#{i : t ≤ T̃ᵢ}`;
* `eventCount d t` / `eventTimes d` — event multiplicities and the (finite) set of event
  times;
* `naJump d s = ΔN(s)/Y(s)` — the Nelson–Aalen increment;
* `nelsonAalen d t = ∑_{s ≤ t} ΔN(s)/Y(s)` — the Nelson–Aalen estimator (Nelson 1969;
  Aalen 1978);
* `kaplanMeier d t = ∏_{s ≤ t} (1 − ΔN(s)/Y(s))` — the Kaplan–Meier product-limit
  estimator, **defined** as the product of one-minus-NA-jumps, so the classical relation
  `KM = ∏(1 − ΔNA)` is structural; the content lemma `nelsonAalen_eq_partial_add_jump`
  identifies `naJump` as the genuine jump of `nelsonAalen`;
* `kaplanMeierSF` / `kaplanMeierMeasure` — Kaplan–Meier as a bona fide (sub-probability)
  law via a Stieltjes function — the classic defect: mass is lost iff the largest
  observation is censored.

Exact finite-sample results only (consistency/Greenwood are designated future milestones):
range, monotonicity, piecewise constancy, the no-censoring reduction to the empirical
survival function, and the self-consistency identity `ΔΛ_{KM}(s) = ΔN(s)/Y(s)`.

**Reference.** E. L. Kaplan and P. Meier, "Nonparametric estimation from incomplete
observations," *J. Amer. Statist. Assoc.* **53** (1958), 457–481, §1–2 (`KM58`); W. Nelson,
"Hazard plotting for incomplete failure data," *J. Qual. Tech.* **1** (1969), 27–52
(`Nelson69`); O. O. Aalen, "Nonparametric inference for a family of counting processes,"
*Ann. Statist.* **6** (1978), 701–726 (`Aalen78`); ABGK §IV.1 (Nelson–Aalen) and §IV.3
(Kaplan–Meier) (verify §).

**Proof formalization notes.** Everything is `Finset` combinatorics over the finitely many
event times; no measure theory except the Stieltjes packaging. The no-censoring reduction is
the one genuinely fiddly telescoping induction (sorted event times; `Y(s_{k+1}) = Y(s_k) −
ΔN(s_k)` holds exactly because nothing is censored between events). Degenerate-input
conventions: `naJump` junk-values by real division (`0/0 = 0`); the empty dataset is excluded
only where it genuinely breaks a statement (`hn : n ≠ 0`, LEAN-ONLY).

**Bibliographic comments.** The product-limit idea is KM58's; the hazard-increment view and
the KM–NA jump relation are Nelson69/Aalen78, unified by the counting-process synthesis of
ABGK.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

variable {n : ℕ}

/-- The **risk-set size** `Y(t) = #{i : t ≤ T̃ᵢ}` (ABGK §IV.1). -/
noncomputable def atRisk (d : Fin n → ℝ × Bool) (t : ℝ) : ℕ :=
  (univ.filter fun i => t ≤ (d i).1).card

/-- The **event multiplicity** `ΔN(t) = #{i : T̃ᵢ = t, Δᵢ = 1}`. -/
noncomputable def eventCount (d : Fin n → ℝ × Bool) (t : ℝ) : ℕ :=
  (univ.filter fun i => (d i).1 = t ∧ (d i).2 = true).card

/-- The (finite) set of observed **event times**. -/
noncomputable def eventTimes (d : Fin n → ℝ × Bool) : Finset ℝ :=
  (univ.filter fun i => (d i).2 = true).image fun i => (d i).1

/-- The **Nelson–Aalen increment** `ΔN(s)/Y(s)` (junk `0/0 = 0` off the event times). -/
noncomputable def naJump (d : Fin n → ℝ × Bool) (s : ℝ) : ℝ :=
  (eventCount d s : ℝ) / (atRisk d s : ℝ)

/-- The **Nelson–Aalen estimator** `Λ̂(t) = ∑_{s ≤ t} ΔN(s)/Y(s)` (`Nelson69`; `Aalen78`;
ABGK §IV.1). -/
noncomputable def nelsonAalen (d : Fin n → ℝ × Bool) (t : ℝ) : ℝ :=
  ∑ s ∈ (eventTimes d).filter (· ≤ t), naJump d s

/-- The **Kaplan–Meier product-limit estimator** `Ŝ(t) = ∏_{s ≤ t} (1 − ΔN(s)/Y(s))`
(`KM58`), defined as the product of one-minus-Nelson–Aalen-jumps — the classical relation
`KM = ∏(1 − ΔNA)` is thereby structural. -/
noncomputable def kaplanMeier (d : Fin n → ℝ × Bool) (t : ℝ) : ℝ :=
  ∏ s ∈ (eventTimes d).filter (· ≤ t), (1 - naJump d s)

/-- Risk sets shrink in time. -/
theorem atRisk_antitone (d : Fin n → ℝ × Bool) : Antitone fun t => atRisk d t := by
  intro a b hab
  refine Finset.card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hab.trans hi

/-- Events at `s` are at risk at `s`. -/
theorem eventCount_le_atRisk (d : Fin n → ℝ × Bool) (s : ℝ) :
    eventCount d s ≤ atRisk d s := by
  refine Finset.card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.1.ge

/-- Membership in `eventTimes` unpacks to an observation which is an event at that time. -/
private lemma exists_of_mem_eventTimes {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d) : ∃ i, (d i).1 = s ∧ (d i).2 = true := by
  rw [eventTimes, Finset.mem_image] at hs
  obtain ⟨i, hi, hval⟩ := hs
  exact ⟨i, hval, (Finset.mem_filter.1 hi).2⟩

/-- At an event time the risk set is nonempty. -/
theorem atRisk_pos_of_mem_eventTimes {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d) : 0 < atRisk d s := by
  obtain ⟨i, hval, -⟩ := exists_of_mem_eventTimes hs
  exact Finset.card_pos.2 ⟨i, by simp [hval]⟩

/-- At an event time there is at least one event. -/
theorem eventCount_pos_of_mem_eventTimes {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d) : 0 < eventCount d s := by
  obtain ⟨i, hval, hdel⟩ := exists_of_mem_eventTimes hs
  exact Finset.card_pos.2 ⟨i, by simp [hval, hdel]⟩

/-- The Nelson–Aalen increment lies in `[0, 1]`. -/
theorem naJump_mem_Icc (d : Fin n → ℝ × Bool) (s : ℝ) : naJump d s ∈ Set.Icc 0 1 := by
  rcases Nat.eq_zero_or_pos (atRisk d s) with h0 | hpos
  · simp [naJump, h0]
  · refine Set.mem_Icc.2 ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    rw [naJump, div_le_one (by exact_mod_cast hpos : (0 : ℝ) < (atRisk d s : ℝ))]
    exact_mod_cast eventCount_le_atRisk d s

/-- The Kaplan–Meier factors lie in `[0, 1]`. -/
private lemma one_sub_naJump_mem_Icc (d : Fin n → ℝ × Bool) (s : ℝ) :
    0 ≤ 1 - naJump d s ∧ 1 - naJump d s ≤ 1 := by
  obtain ⟨h0, h1⟩ := Set.mem_Icc.1 (naJump_mem_Icc d s)
  constructor <;> linarith

/-- Any product of Kaplan–Meier factors lies in `[0, 1]`. -/
private lemma prod_one_sub_naJump_mem_Icc (d : Fin n → ℝ × Bool) (F : Finset ℝ) :
    0 ≤ ∏ s ∈ F, (1 - naJump d s) ∧ ∏ s ∈ F, (1 - naJump d s) ≤ 1 :=
  ⟨Finset.prod_nonneg fun s _ => (one_sub_naJump_mem_Icc d s).1,
    Finset.prod_le_one (fun s _ => (one_sub_naJump_mem_Icc d s).1)
      fun s _ => (one_sub_naJump_mem_Icc d s).2⟩

/-- At an event time the truncated set of event times splits off its top point. -/
private lemma filter_le_eq_insert {d : Fin n → ℝ × Bool} {s : ℝ} (hs : s ∈ eventTimes d) :
    (eventTimes d).filter (· ≤ s) = insert s ((eventTimes d).filter (· < s)) := by
  ext u
  simp only [Finset.mem_insert, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inr ⟨hu, h⟩
    · exact Or.inl h
  · rintro (rfl | ⟨hu, hlt⟩)
    · exact ⟨hs, le_rfl⟩
    · exact ⟨hu, hlt.le⟩

/-- **`naJump` is the genuine jump of `nelsonAalen`** at an event time: the estimator at `s`
is its strict-past partial sum plus the increment (the content behind `KM = ∏(1 − ΔNA)`;
ABGK §IV.1 vs §IV.3). -/
theorem nelsonAalen_eq_partial_add_jump {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d) :
    nelsonAalen d s = (∑ u ∈ (eventTimes d).filter (· < s), naJump d u) + naJump d s := by
  rw [nelsonAalen, filter_le_eq_insert hs,
    Finset.sum_insert (by simp), add_comm]

/-- Kaplan–Meier takes values in `[0, 1]` (`KM58`). -/
theorem kaplanMeier_mem_Icc (d : Fin n → ℝ × Bool) (t : ℝ) :
    kaplanMeier d t ∈ Set.Icc 0 1 :=
  Set.mem_Icc.2 (prod_one_sub_naJump_mem_Icc d _)

/-- Kaplan–Meier is antitone (`KM58`). -/
theorem antitone_kaplanMeier (d : Fin n → ℝ × Bool) : Antitone (kaplanMeier d) := by
  intro a b hab
  have hsub : (eventTimes d).filter (· ≤ a) ⊆ (eventTimes d).filter (· ≤ b) := by
    intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, hu.2.trans hab⟩
  have h := Finset.prod_sdiff (f := fun s => 1 - naJump d s) hsub
  simp only [kaplanMeier]
  rw [← h]
  exact mul_le_of_le_one_left (prod_one_sub_naJump_mem_Icc d _).1
    (prod_one_sub_naJump_mem_Icc d _).2

/-- Kaplan–Meier only sees the event times through the truncation `{s ∈ eventTimes | s ≤ ·}`. -/
private lemma kaplanMeier_eq_prod_of_filter_eq {d : Fin n → ℝ × Bool} {u : ℝ} {F : Finset ℝ}
    (h : (eventTimes d).filter (· ≤ u) = F) :
    kaplanMeier d u = ∏ s ∈ F, (1 - naJump d s) := by
  simp only [kaplanMeier, h]

/-- Kaplan–Meier is right-locally constant (piecewise constancy between event times; whence
right-continuity without any filter bookkeeping). -/
theorem kaplanMeier_eventually_constant_right (d : Fin n → ℝ × Bool) (t : ℝ) :
    ∃ ε > 0, ∀ u ∈ Set.Ico t (t + ε), kaplanMeier d u = kaplanMeier d t := by
  have key : ∀ (ε : ℝ), 0 < ε → (∀ v ∈ eventTimes d, t < v → t + ε ≤ v) →
      ∀ u ∈ Set.Ico t (t + ε), kaplanMeier d u = kaplanMeier d t := by
    intro ε _ hgap u hu
    refine kaplanMeier_eq_prod_of_filter_eq (F := (eventTimes d).filter (· ≤ t)) ?_
    ext v
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hv
    refine ⟨fun hvu => ?_, fun hvt => hvt.trans hu.1⟩
    by_contra hc
    exact absurd (hvu.trans_lt hu.2) (not_lt.2 (hgap v hv (not_le.1 hc)))
  rcases ((eventTimes d).filter (t < ·)).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, key 1 one_pos fun v hv hvt => ?_⟩
    exact absurd (Finset.mem_filter.2 ⟨hv, hvt⟩) (by simp [hemp])
  · have hmem := Finset.min'_mem _ hne
    have hmt : t < ((eventTimes d).filter (t < ·)).min' hne := (Finset.mem_filter.1 hmem).2
    refine ⟨((eventTimes d).filter (t < ·)).min' hne - t, by linarith,
      key _ (by linarith) fun v hv hvt => ?_⟩
    have := Finset.min'_le _ v (Finset.mem_filter.2 ⟨hv, hvt⟩)
    linarith

/-- Kaplan–Meier as a Stieltjes function: `t ↦ 1 − Ŝ(t)` (monotone by
`antitone_kaplanMeier`, right-continuous by piecewise constancy). -/
noncomputable def kaplanMeierSF (d : Fin n → ℝ × Bool) : StieltjesFunction ℝ where
  toFun t := 1 - kaplanMeier d t
  mono' a b hab := by have := antitone_kaplanMeier d hab; linarith
  right_continuous' t := by
    obtain ⟨ε, hε, hcon⟩ := kaplanMeier_eventually_constant_right d t
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ico_mem_nhdsGE (show t < t + ε by linarith)] with u hu
    rw [hcon u hu]

@[simp]
theorem kaplanMeierSF_apply (d : Fin n → ℝ × Bool) (t : ℝ) :
    kaplanMeierSF d t = 1 - kaplanMeier d t := rfl

/-- Kaplan–Meier is left-locally constant, with the strict-past product as its value. -/
private lemma kaplanMeier_eventually_constant_left (d : Fin n → ℝ × Bool) (t : ℝ) :
    ∃ ε > 0, ∀ u ∈ Set.Ioo (t - ε) t,
      kaplanMeier d u = ∏ s ∈ (eventTimes d).filter (· < t), (1 - naJump d s) := by
  have key : ∀ ε : ℝ, 0 < ε → (∀ v ∈ eventTimes d, v < t → v ≤ t - ε) →
      ∀ u ∈ Set.Ioo (t - ε) t,
        kaplanMeier d u = ∏ s ∈ (eventTimes d).filter (· < t), (1 - naJump d s) := by
    intro ε _ hgap u hu
    refine kaplanMeier_eq_prod_of_filter_eq ?_
    ext v
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hv
    exact ⟨fun hvu => hvu.trans_lt hu.2, fun hvt => (hgap v hv hvt).trans hu.1.le⟩
  rcases ((eventTimes d).filter (· < t)).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, key 1 one_pos fun v hv hvt => ?_⟩
    exact absurd (Finset.mem_filter.2 ⟨hv, hvt⟩ :
      v ∈ (eventTimes d).filter (· < t)) (by simp [hemp])
  · have hmem := Finset.max'_mem _ hne
    have hMt : ((eventTimes d).filter (· < t)).max' hne < t := (Finset.mem_filter.1 hmem).2
    refine ⟨t - ((eventTimes d).filter (· < t)).max' hne, by linarith,
      key _ (by linarith) fun v hv hvt => ?_⟩
    have := Finset.le_max' _ v (Finset.mem_filter.2 ⟨hv, hvt⟩ :
      v ∈ (eventTimes d).filter (· < t))
    linarith

/-- The left limit of the Kaplan–Meier Stieltjes function is `1 − Ŝ(t−)`. -/
private lemma leftLim_kaplanMeierSF (d : Fin n → ℝ × Bool) (t : ℝ) :
    Function.leftLim (kaplanMeierSF d) t
      = 1 - ∏ s ∈ (eventTimes d).filter (· < t), (1 - naJump d s) := by
  obtain ⟨ε, hε, hcon⟩ := kaplanMeier_eventually_constant_left d t
  refine leftLim_eq_of_tendsto (nhdsLT_neBot t).ne ?_
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsLT (show t - ε < t by linarith)] with u hu
  rw [kaplanMeierSF_apply, hcon u hu]

/-- Below every event time Kaplan–Meier is still one. -/
private lemma kaplanMeier_eq_one_of_lt {d : Fin n → ℝ × Bool} {t : ℝ}
    (h : ∀ s ∈ eventTimes d, t < s) : kaplanMeier d t = 1 := by
  rw [kaplanMeier_eq_prod_of_filter_eq (F := ∅) ?_, Finset.prod_empty]
  exact Finset.filter_eq_empty_iff.2 fun v hv => not_le.2 (h v hv)

/-- The full product of Kaplan–Meier factors — the terminal value `Ŝ(∞)`. -/
private noncomputable def kmLimit (d : Fin n → ℝ × Bool) : ℝ :=
  ∏ s ∈ eventTimes d, (1 - naJump d s)

private lemma tendsto_kaplanMeierSF_atBot (d : Fin n → ℝ × Bool) :
    Filter.Tendsto (kaplanMeierSF d) Filter.atBot (nhds 0) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ s ∈ eventTimes d, a < s := by
    rcases (eventTimes d).eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨(eventTimes d).min' h - 1, fun s hs => by
        have := (eventTimes d).min'_le s hs; linarith⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_le_atBot a] with t ht
  rw [kaplanMeierSF_apply, kaplanMeier_eq_one_of_lt fun s hs => lt_of_le_of_lt ht (ha s hs),
    sub_self]

private lemma tendsto_kaplanMeierSF_atTop (d : Fin n → ℝ × Bool) :
    Filter.Tendsto (kaplanMeierSF d) Filter.atTop (nhds (1 - kmLimit d)) := by
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s ∈ eventTimes d, s ≤ b := by
    rcases (eventTimes d).eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨(eventTimes d).max' h, fun s hs => (eventTimes d).le_max' s hs⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop b] with t ht
  rw [kaplanMeierSF_apply,
    kaplanMeier_eq_prod_of_filter_eq (F := eventTimes d)
      (Finset.filter_true_of_mem fun v hv => (hb v hv).trans ht)]
  rfl

/-- **Kaplan–Meier as a law**: the Stieltjes measure of `1 − Ŝ` (`KM58` — the product-limit
estimate *is* a distribution, possibly defective). -/
noncomputable def kaplanMeierMeasure (d : Fin n → ℝ × Bool) : Measure ℝ :=
  (kaplanMeierSF d).measure

/-- The Kaplan–Meier law is a sub-event-time law on nonnegative data — total mass at most
one (the classic defect: mass is lost exactly when the largest observation is censored). -/
theorem isSubEventTimeLaw_kaplanMeierMeasure (d : Fin n → ℝ × Bool)
    -- USER-INPUT: observation times are nonnegative; KM58 §1
    (hd : ∀ i, 0 ≤ (d i).1) :
    IsSubEventTimeLaw (kaplanMeierMeasure d) := by
  have hEvent : ∀ s ∈ eventTimes d, 0 ≤ s := by
    intro s hs
    obtain ⟨i, hval, -⟩ := exists_of_mem_eventTimes hs
    exact hval ▸ hd i
  constructor
  · rw [kaplanMeierMeasure,
      StieltjesFunction.measure_univ _ (tendsto_kaplanMeierSF_atBot d)
        (tendsto_kaplanMeierSF_atTop d)]
    refine ENNReal.ofReal_le_one.2 ?_
    have := (prod_one_sub_naJump_mem_Icc d (eventTimes d)).1
    simp only [kmLimit] at *
    linarith
  · rw [kaplanMeierMeasure,
      StieltjesFunction.measure_Iio _ (tendsto_kaplanMeierSF_atBot d) 0,
      leftLim_kaplanMeierSF d 0]
    rw [Finset.filter_eq_empty_iff.2 fun v hv => not_lt.2 (hEvent v hv)]
    simp

/-- **No-censoring reduction** (`KM58 §1`): with every observation an event, Kaplan–Meier is
the empirical survival function `#{i : t < T̃ᵢ}/n`. -/
theorem kaplanMeier_of_no_censoring {d : Fin n → ℝ × Bool}
    -- USER-INPUT: no censoring; KM58 §1
    (hall : ∀ i, (d i).2 = true)
    -- LEAN-ONLY: nonempty dataset (0/0 junk breaks the n = 0 corner)
    (hn : n ≠ 0) (t : ℝ) :
    kaplanMeier d t = ((univ.filter fun i => t < (d i).1).card : ℝ) / n := by
  sorry

/-- **Self-consistency** (ABGK §IV.3 (verify §)): the hazard jump of the Kaplan–Meier law at
an event time inside its support is the Nelson–Aalen increment — the estimator solves the
model's own hazard identity. -/
theorem cumHazardJump_kaplanMeierMeasure {d : Fin n → ℝ × Bool} {s : ℝ}
    (hs : s ∈ eventTimes d)
    -- USER-INPUT: the left limit of KM at s is positive (inside the support); ABGK §IV.3
    (hpos : 0 < ∏ u ∈ (eventTimes d).filter (· < s), (1 - naJump d u)) :
    cumHazardJump (kaplanMeierMeasure d) s = ENNReal.ofReal (naJump d s) := by
  sorry

end StatLean.StatisticalModels.Survival
