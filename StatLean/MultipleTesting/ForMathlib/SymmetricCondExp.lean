import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic

/-!
# Symmetric conditional expectation of an exchangeable Bool vector — `ForMathlib`

The **exchangeable / sampling-without-replacement** identity behind the knock-off supermartingale
step (Lu-BDA §19): for i.i.d. fair `Bool` variables `σ : Fin k → Ω → Bool`, the conditional
expectation of the indicator of *one* coordinate `i₀`, given the **count** σ-algebra
`σ(#{i : σ i = true})`, equals `count / k`.

Mathlib has **no** exchangeability / de Finetti / Pólya / hypergeometric conditional-expectation
support, so this is built from scratch. It is the single Mathlib-absent ingredient the knock-off
FDR proof (`count_condExp`, `Knockoff/Step.lean`) consumes — and is independently upstreamable.

## Proof route

We verify, via `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`, that `count / k` *is* the
conditional expectation of `𝟙(σ i₀ = true)` given the count σ-algebra. The defining set-integral
identity reduces (writing `count = ∑ l, 𝟙(σ l = true)` and pulling the sum out of the integral) to
the **exchangeability fact** that, for any set `s` in the count σ-algebra,
`μ(s ∩ {σ i = true})` does not depend on the coordinate `i`. The latter is established by
expanding `s ∩ {σ i = true}` over the partition of `Ω` by the full "type vector"
`typeVec ω = {i : σ i ω = true}` — each cell has measure `(1/2)^k` by independence + fairness — and
observing that the index sets are matched by the coordinate transposition `Equiv.swap i j`.
-/

-- The exchangeability events are described by arbitrary predicates on the (undecidable) type
-- vector, so the `Finset.filter`s in these statements genuinely require classical decidability.
set_option linter.style.openClassical false

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hamming weight (number of `true` entries) of the `Bool` sample `fun i => σ i ω`. -/
noncomputable def signCount {k : ℕ} (σ : Fin k → Ω → Bool) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i => σ i ω = true)).card

/-- `signCount σ` is measurable when each coordinate `σ i` is measurable. -/
lemma measurable_signCount {k : ℕ} (σ : Fin k → Ω → Bool)
    (hσ : ∀ i, Measurable (σ i)) : Measurable (signCount σ) := by
  have hrw : signCount σ = fun ω => ∑ i, (if σ i ω = true then (1 : ℕ) else 0) := by
    funext ω; simp only [signCount, Finset.card_filter]
  rw [hrw]
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Measurable.ite (hσ i (measurableSet_singleton true)) measurable_const measurable_const

/-- The "type vector": the set of coordinates that are `true` for the sample `ω`.
By construction `signCount σ ω = (typeVec σ ω).card`. -/
def typeVec {k : ℕ} (σ : Fin k → Ω → Bool) (ω : Ω) : Finset (Fin k) :=
  Finset.univ.filter (fun i => σ i ω = true)

private lemma mem_typeVec {k : ℕ} (σ : Fin k → Ω → Bool) (ω : Ω) (i : Fin k) :
    i ∈ typeVec σ ω ↔ σ i ω = true := by
  simp [typeVec]

/-- The event "the sample's true-coordinates are exactly `T`". -/
def evtSet {k : ℕ} (σ : Fin k → Ω → Bool) (T : Finset (Fin k)) : Set Ω :=
  ⋂ i, (σ i) ⁻¹' (if i ∈ T then ({true} : Set Bool) else {false})

private lemma mem_evtSet {k : ℕ} (σ : Fin k → Ω → Bool) (T : Finset (Fin k)) (ω : Ω) :
    ω ∈ evtSet σ T ↔ typeVec σ ω = T := by
  simp only [evtSet, Set.mem_iInter, Set.mem_preimage]
  rw [Finset.ext_iff]
  refine forall_congr' (fun i => ?_)
  rw [mem_typeVec]
  by_cases hi : i ∈ T <;> simp [hi, Set.mem_singleton_iff, Bool.not_eq_true]

private lemma measurableSet_evtSet {k : ℕ} {σ : Fin k → Ω → Bool}
    (hσ : ∀ i, Measurable (σ i)) (T : Finset (Fin k)) : MeasurableSet (evtSet σ T) := by
  unfold evtSet
  apply MeasurableSet.iInter
  intro i
  apply hσ i
  exact MeasurableSet.of_discrete

/-- Each cell of the type-vector partition has measure `(1/2)^k`: this is independence + fairness
(`μ(σ i = true) = μ(σ i = false) = 1/2`). -/
private lemma measure_evtSet {k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : Fin k → Ω → Bool} (hσ : ∀ i, Measurable (σ i)) (hindep : iIndepFun σ μ)
    (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (T : Finset (Fin k)) :
    μ (evtSet σ T) = (1 / 2 : ℝ≥0∞) ^ k := by
  have hAi : ∀ i, MeasurableSet {ω | σ i ω = true} :=
    fun i => hσ i (measurableSet_singleton true)
  have hcomap : ∀ i, MeasurableSet[(inferInstance : MeasurableSpace Bool).comap (σ i)]
      ((σ i) ⁻¹' (if i ∈ T then ({true} : Set Bool) else {false})) :=
    fun i => ⟨_, MeasurableSet.of_discrete, rfl⟩
  have hprod : μ (evtSet σ T)
      = ∏ i, μ ((σ i) ⁻¹' (if i ∈ T then ({true} : Set Bool) else {false})) :=
    iIndepFun.meas_iInter hindep hcomap
  rw [hprod]
  have hfac : ∀ i, μ ((σ i) ⁻¹' (if i ∈ T then ({true} : Set Bool) else {false})) = 1 / 2 := by
    intro i
    by_cases hi : i ∈ T
    · rw [if_pos hi]; exact hfair i
    · rw [if_neg hi]
      have hc : (σ i) ⁻¹' ({false} : Set Bool) = {ω | σ i ω = true}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
          Set.mem_setOf_eq, Bool.not_eq_true]
      rw [hc, prob_compl_eq_one_sub (hAi i), hfair i]
      exact ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.add_halves 1).symm
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Master measure computation.** The measure of any event described by a property `Q` of the
type vector is `(#allowed type vectors) · (1/2)^k`. -/
private lemma measure_setOf_typeVec {k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : Fin k → Ω → Bool} (hσ : ∀ i, Measurable (σ i)) (hindep : iIndepFun σ μ)
    (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (Q : Finset (Fin k) → Prop) :
    μ {ω | Q (typeVec σ ω)}
      = ((Finset.univ.powerset.filter Q).card) • (1 / 2 : ℝ≥0∞) ^ k := by
  have hset : {ω | Q (typeVec σ ω)}
      = ⋃ T ∈ (Finset.univ.powerset.filter Q), evtSet σ T := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, mem_evtSet, exists_prop]
    constructor
    · intro hQ; exact ⟨typeVec σ ω, hQ, rfl⟩
    · rintro ⟨T, hQT, rfl⟩; exact hQT
  have hdisj : (↑(Finset.univ.powerset.filter Q) : Set (Finset (Fin k))).PairwiseDisjoint
      (evtSet σ) := by
    intro T _ T' _ hne
    change Disjoint (evtSet σ T) (evtSet σ T')
    rw [Set.disjoint_left]
    intro ω hω hω'
    exact hne (((mem_evtSet σ T ω).mp hω).symm.trans ((mem_evtSet σ T' ω).mp hω'))
  have hmeas : ∀ T ∈ Finset.univ.powerset.filter Q, MeasurableSet (evtSet σ T) :=
    fun T _ => measurableSet_evtSet hσ T
  rw [hset, measure_biUnion_finset hdisj hmeas,
    Finset.sum_congr rfl (fun T _ => measure_evtSet μ hσ hindep hfair T), Finset.sum_const]

/-- **Exchangeability.** For any set in the count σ-algebra, `μ(s ∩ {σ i = true})` is independent of
the coordinate `i`. -/
private lemma measure_inter_swap {k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : Fin k → Ω → Bool} (hσ : ∀ i, Measurable (σ i)) (hindep : iIndepFun σ μ)
    (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (i j : Fin k) (s : Set Ω)
    (hs : MeasurableSet[MeasurableSpace.comap (signCount σ) inferInstance] s) :
    μ (s ∩ {ω | σ i ω = true}) = μ (s ∩ {ω | σ j ω = true}) := by
  obtain ⟨B, -, rfl⟩ := hs
  have hset : ∀ l : Fin k, signCount σ ⁻¹' B ∩ {ω | σ l ω = true}
              = {ω | (fun T => T.card ∈ B ∧ l ∈ T) (typeVec σ ω)} := by
    intro l
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, signCount, typeVec,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset i, hset j, measure_setOf_typeVec μ hσ hindep hfair (fun T => T.card ∈ B ∧ i ∈ T),
    measure_setOf_typeVec μ hσ hindep hfair (fun T => T.card ∈ B ∧ j ∈ T)]
  congr 1
  -- the coordinate transposition `swap i j` matches the two index sets
  apply Finset.card_equiv ((Equiv.swap i j).finsetCongr)
  intro T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    Equiv.finsetCongr_apply, Finset.card_map, Finset.mem_map_equiv, Equiv.symm_swap,
    Equiv.swap_apply_right]

/-- **Exchangeable coordinate conditional expectation** (sampling-without-replacement / Pólya).
For i.i.d. fair `Bool` variables `σ : Fin k → Ω → Bool`, the conditional expectation of the
indicator of coordinate `i₀` given the count σ-algebra `σ(signCount σ)` equals `signCount σ / k`.

The brick the knock-off supermartingale step (`count_condExp`, Lu-BDA §19) consumes. -/
theorem condExp_coord_eq_count_div {k : ℕ} (hk : 0 < k)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Fin k → Ω → Bool)
    (hσ : ∀ i, Measurable (σ i)) (hindep : iIndepFun σ μ)
    (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (i₀ : Fin k) :
    μ[(fun ω => if σ i₀ ω then (1 : ℝ) else 0) |
        MeasurableSpace.comap (signCount σ) inferInstance]
      =ᵐ[μ] fun ω => (signCount σ ω : ℝ) / (k : ℝ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0' : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hAmeas : ∀ l, MeasurableSet {ω | σ l ω = true} :=
    fun l => hσ l (measurableSet_singleton true)
  have hsle : ∀ ω, signCount σ ω ≤ k := by
    intro ω
    simpa [signCount, Finset.card_univ] using
      Finset.card_filter_le (Finset.univ) (fun i => σ i ω = true)
  have hmle : MeasurableSpace.comap (signCount σ) inferInstance ≤ mΩ :=
    measurable_iff_comap_le.mp (measurable_signCount σ hσ)
  have hg_amb : Measurable (fun ω => (signCount σ ω : ℝ) / (k : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ) / (k : ℝ))).comp (measurable_signCount σ hσ)
  have hFint : ∀ l, Integrable (fun ω => if σ l ω then (1 : ℝ) else 0) μ := by
    intro l
    refine (integrable_const (1 : ℝ)).mono'
      (Measurable.ite (hAmeas l) measurable_const measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    split_ifs <;> simp
  have hg_int : Integrable (fun ω => (signCount σ ω : ℝ) / (k : ℝ)) μ := by
    refine (integrable_const (1 : ℝ)).mono' hg_amb.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hk0.le), div_le_one hk0]
    exact_mod_cast hsle ω
  have hsign_m : Measurable[MeasurableSpace.comap (signCount σ) inferInstance] (signCount σ) :=
    measurable_iff_comap_le.mpr le_rfl
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap (signCount σ) inferInstance]
      (fun ω => (signCount σ ω : ℝ) / (k : ℝ)) μ :=
    ((measurable_from_nat (f := fun n : ℕ => (n : ℝ) / (k : ℝ))).comp hsign_m).aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmle (hFint i₀)
      (fun s _ _ => hg_int.integrableOn) ?_ hgm).symm
  intro s hs _
  have hsm0 : MeasurableSet s := hmle s hs
  have hF : ∀ l, ∫ ω in s, (if σ l ω then (1 : ℝ) else 0) ∂μ
              = (μ (s ∩ {ω | σ l ω = true})).toReal := by
    intro l
    have hind : (fun ω => if σ l ω then (1 : ℝ) else 0)
              = {ω | σ l ω = true}.indicator (fun _ => (1 : ℝ)) := by
      funext ω; rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]
    rw [hind, setIntegral_indicator (hAmeas l), setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hgsum : ∀ ω, (signCount σ ω : ℝ) / (k : ℝ)
              = (1 / (k : ℝ)) * ∑ l, (if σ l ω then (1 : ℝ) else 0) := by
    intro ω
    have hcard : (signCount σ ω : ℝ) = ∑ l, (if σ l ω then (1 : ℝ) else 0) := by
      simp only [signCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    rw [hcard]; ring
  have hLHS : ∫ ω in s, (signCount σ ω : ℝ) / (k : ℝ) ∂μ
            = (1 / (k : ℝ)) * ∑ l, (μ (s ∩ {ω | σ l ω = true})).toReal := by
    rw [setIntegral_congr_fun hsm0 (fun ω _ => hgsum ω), integral_const_mul,
       integral_finset_sum Finset.univ (fun l _ => (hFint l).integrableOn)]
    simp_rw [hF]
  have hsum : ∑ l, (μ (s ∩ {ω | σ l ω = true})).toReal
            = (k : ℝ) * (μ (s ∩ {ω | σ i₀ ω = true})).toReal := by
    rw [Finset.sum_congr rfl (fun l _ =>
        congrArg ENNReal.toReal (measure_inter_swap μ hσ hindep hfair l i₀ s hs)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change ∫ ω in s, (signCount σ ω : ℝ) / (k : ℝ) ∂μ
        = ∫ ω in s, (if σ i₀ ω then (1 : ℝ) else 0) ∂μ
  rw [hLHS, hF i₀, hsum, one_div, ← mul_assoc, inv_mul_cancel₀ hk0', one_mul]

/-- Count of `true` coordinates of the sample `ω` **restricted to a subset** `T`. -/
noncomputable def subsetCount {ι : Type*} [DecidableEq ι] (σ : ι → Ω → Bool)
    (T : Finset ι) (ω : Ω) : ℕ :=
  (T.filter (fun i => σ i ω = true)).card

/-- **Exchangeable coordinate conditional expectation over a subset.** For an i.i.d.-fair `Bool`
family `σ` indexed by an arbitrary fintype `ι`, fix a subset `T` and a coordinate `i₀ ∈ T`. The
conditional expectation of the indicator of `i₀` given the σ-algebra generated by the *count over
`T`* (`#{i ∈ T : σ i = true}`) equals `(count over T)/|T|`. Obtained from
`condExp_coord_eq_count_div` by reindexing the subfamily `(σ i)_{i∈T}` along `T ≃ Fin |T|`. -/
theorem condExp_coord_eq_subsetCount_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : ι → Ω → Bool)
    (hσ : ∀ i, Measurable (σ i)) (hindep : iIndepFun σ μ)
    (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2)
    (T : Finset ι) (hT : 0 < T.card) (i₀ : ι) (hi₀ : i₀ ∈ T) :
    μ[(fun ω => if σ i₀ ω then (1 : ℝ) else 0) |
        MeasurableSpace.comap (subsetCount σ T) inferInstance]
      =ᵐ[μ] fun ω => (subsetCount σ T ω : ℝ) / (T.card : ℝ) := by
  classical
  -- Reindex the subfamily `(σ i)_{i ∈ T}` along the enumeration `g : Fin T.card → ι`.
  set e : {x // x ∈ T} ≃ Fin T.card := T.equivFin with he
  set g : Fin T.card → ι := fun k => ((e.symm k : {x // x ∈ T}) : ι) with hg
  have hg_inj : Function.Injective g :=
    Subtype.val_injective.comp e.symm.injective
  set τ : Fin T.card → Ω → Bool := fun k => σ (g k) with hτ
  have hτmeas : ∀ k, Measurable (τ k) := fun k => hσ (g k)
  have hτindep : iIndepFun τ μ := hindep.precomp hg_inj
  have hτfair : ∀ k, μ {ω | τ k ω = true} = 1 / 2 := fun k => hfair (g k)
  set k₀ : Fin T.card := e ⟨i₀, hi₀⟩ with hk₀
  have hgk₀ : g k₀ = i₀ := by
    simp only [hg, hk₀, Equiv.symm_apply_apply]
  -- The count over `T` is the `signCount` of the reindexed family.
  have hcount : ∀ ω, signCount τ ω = subsetCount σ T ω := by
    intro ω
    simp only [signCount, subsetCount]
    refine Finset.card_bij (fun k _ => g k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hτ] at hk
      simp only [Finset.mem_filter]
      exact ⟨(e.symm k).property, hk⟩
    · intro a _ b _ hab; exact hg_inj hab
    · intro b hb
      simp only [Finset.mem_filter] at hb
      refine ⟨e ⟨b, hb.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hτ, hg,
          Equiv.symm_apply_apply]
        exact hb.2
      · simp only [hg, Equiv.symm_apply_apply]
  have hcountfun : signCount τ = subsetCount σ T := funext hcount
  have happ := condExp_coord_eq_count_div hT μ τ hτmeas hτindep hτfair k₀
  -- Rewrite `τ k₀ = σ i₀`, `signCount τ = subsetCount σ T`.
  rw [hcountfun] at happ
  simp only [hτ, hgk₀] at happ
  exact happ

end StatLean.MultipleTesting
