import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.ForMathlib.SymmetricCondExp
import StatLean.MultipleTesting.ForMathlib.BinomialRatio
import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import Mathlib.Probability.Independence.Basic

/-!
# Storey's q-value procedure — FDR control (Candès, Lecture 7, §7.4, Theorem 3)

Storey's adaptive procedure estimates the null proportion and thresholds the p-values on `[0,1/2]`.
With the rejection count `R(t) = countLE p t` and false-rejection count `V(t) = nullCountLE H₀ p t`:

* `storeyPiZero` — the null-proportion estimate `π̂₀ = (1 + n − R(1/2)) / (n/2)` (the `+1` keeps the
  martingale denominator strictly positive — see the proof);
* `storeyFDRhat q t` — the estimated FDR `π̂₀ · n t / (R(t) ∨ 1)`;
* `storeyThreshold q` — `τ = sup{ t ≤ 1/2 : storeyFDRhat q t ≤ q }`;
* `storeyRejects q` — reject `{ i : pᵢ ≤ τ }`.

**Main result** (`storey_fdr_le`, Candès L7 §7.4, Theorem 3): for independent uniform null p-values,
`FDR ≤ q`.

*Proof.* The pointwise bound `FDP(τ) ≤ q · (V(τ)/τ) · (1/2)/(1+n₀−V(1/2))` (`storey_FDP_le_bound`,
**fully proved** from threshold attainment + the count split `R(1/2)+n₀ ≤ V(1/2)+n`) integrates to
`E[FDP(τ)] ≤ q · ∫ (V(τ)/τ)·w`; the reverse-MG optional-stopping identity gives
`∫ (V(τ)/τ)·w = ∫ V(1/2)/(1+n₀−V(1/2))`, which the binomial null-count law bounds by
`1 − 2^{−n₀} ≤ 1`, whence `E[FDP(τ)] ≤ q`. **The assembly (`storey_fdr_le`) and the pointwise bound
are verified here**; the irreducible probabilistic content is isolated into three sharp, correctly
stated, documented named `sorry`s:

* `storey_reverseMG_ost` — the reverse-martingale optional-stopping identity (integrability of
  `(V(τ)/τ)·w` plus `∫ (V(τ)/τ)·w = ∫ V(1/2)/(1+n₀−V(1/2))`); Mathlib lacks continuous-time
  backwards-martingale support, and the faithful discrete reformulation over the null order
  statistics (the uniform analogue of the knock-off `condExp_coord_eq_count_div`) is a
  self-contained development of its own (cf. `Knockoff/Supermartingale.lean`).
* `storey_binom_bound` — the binomial null-count law `∫ V(1/2)/(1+n₀−V(1/2)) ≤ 1`; the finite-sum
  algebra reuses `ForMathlib/BinomialRatio` (`binom_ratio_sum_le_one`), the missing piece being the
  law `V(1/2) ∼ Bin(n₀,1/2)`.
* `storey_threshold_attained` — the right-continuity attainment `storeyFDRhat τ ≤ q` at the `sSup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- Storey's null-proportion estimate `π̂₀ = (1 + n − R(1/2)) / (n/2)` (Candès L7 §7.4). -/
noncomputable def storeyPiZero (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (1 + (n : ℝ) - (countLE p (1 / 2) ω : ℝ)) / ((n : ℝ) / 2)

/-- Storey's estimated FDR at threshold `t`: `π̂₀ · n t / (R(t) ∨ 1)` (Candès L7 §7.4). -/
noncomputable def storeyFDRhat (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  storeyPiZero p ω * (n : ℝ) * t / (max (countLE p t ω : ℝ) 1)

/-- Storey's data-dependent threshold `τ = sup{ t ≤ 1/2 : storeyFDRhat q t ≤ q }`
(Candès L7 §7.4). -/
noncomputable def storeyThreshold (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q}

/-- Storey's rejection set: reject `{ i : pᵢ ≤ τ }` (Candès L7 §7.4). -/
noncomputable def storeyRejects (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ω ≤ storeyThreshold p q ω)

/-! ## The reverse-martingale weight and the two integrands of the optional-stopping identity

The optional-stopping argument runs on the backwards martingale `M(t) = V(t)/t` over `t ∈ (0,1/2]`,
carrying the **`𝒢_{1/2}`-measurable weight** `w(ω) = (1/2)/(1 + n₀ − V(1/2))` (the `+1` from
`storeyPiZero` keeps the denominator `≥ 1`, hence strictly positive). Two integrands matter:

* `storeyLHSint = (V(τ)/τ)·w` — the stopped value carrying the weight; this is what the Storey FDP
  is bounded by (`storey_FDP_le_bound`).
* `storeyRHSint = V(1/2)/(1 + n₀ − V(1/2))` — the value of the same quantity at the top of the
  backwards filtration `t = 1/2` (using `(V(1/2)/(1/2))·w = 2·V(1/2)·w = V(1/2)/(1+n₀−V(1/2))`).

The reverse-MG optional-stopping identity (`storey_reverseMG_ost`) is `∫ LHS = ∫ RHS`, and the
binomial null-count law (`storey_binom_bound`) is `∫ RHS ≤ 1`. -/

/-- The strictly-positive Storey denominator `1 + n₀ − V(1/2)` (`n₀ = H₀.card`). The `+1` of
`storeyPiZero` is what makes this `≥ 1`. -/
private noncomputable def storeyDenom (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  1 + (H₀.card : ℝ) - (nullCountLE H₀ p (1 / 2) ω : ℝ)

private lemma nullCountLE_le_card (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    nullCountLE H₀ p t ω ≤ H₀.card := Finset.card_filter_le _ _

private lemma storeyDenom_ge_one (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) :
    1 ≤ storeyDenom H₀ p ω := by
  unfold storeyDenom
  have : (nullCountLE H₀ p (1 / 2) ω : ℝ) ≤ (H₀.card : ℝ) := by
    exact_mod_cast nullCountLE_le_card H₀ p (1 / 2) ω
  linarith

private lemma storeyDenom_pos (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) :
    0 < storeyDenom H₀ p ω := lt_of_lt_of_le one_pos (storeyDenom_ge_one H₀ p ω)

/-- The weighted stopped value `(V(τ)/τ)·w`, with `w = (1/2)/(1+n₀−V(1/2))` the `𝒢_{1/2}`-measurable
weight (`τ = storeyThreshold p q ω`). -/
private noncomputable def storeyLHSint (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) :
    ℝ :=
  ((nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ) / storeyThreshold p q ω)
    * ((1 / 2) / storeyDenom H₀ p ω)

/-- The top-of-filtration value `V(1/2)/(1+n₀−V(1/2))`, equal to `(V(1/2)/(1/2))·w`. Bounded by
`n₀`, hence integrable; its integral is `≤ 1` by the binomial null-count law (`storey_binom_bound`).
-/
private noncomputable def storeyRHSint (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (nullCountLE H₀ p (1 / 2) ω : ℝ) / storeyDenom H₀ p ω

/-- **Backwards-martingale optional stopping for the Storey threshold** (the martingale-theoretic
core of Theorem 3): for independent uniform null p-values, the weighted stopped value `(V(τ)/τ)·w`
is integrable and `∫ (V(τ)/τ)·w = ∫ V(1/2)/(1+n₀−V(1/2))`, where `V(t) = nullCountLE H₀ p t`,
`τ = storeyThreshold p q`, `w = (1/2)/(1+n₀−V(1/2))` is the `𝒢_{1/2}`-measurable weight, and the
right side is `(V(1/2)/(1/2))·w`. This is Doob's optional stopping on the backwards martingale
`{V(t)/t}_{t∈(0,1/2]}` against the `𝒢_{1/2}`-measurable weight `w` (tower property: `E[V(τ)/τ |
𝒢_{1/2}] = V(1/2)/(1/2)`).

**Documented named `sorry`.** Mathlib lacks continuous-time backwards-martingale / optional-stopping
support; the faithful discrete reformulation over the null order statistics (the uniform analogue of
the knock-off `condExp_coord_eq_count_div` — conditional on `V(1/2)=m`, the `m` nulls `≤ 1/2` are
i.i.d. `Uniform[0,1/2]`, so `V(t)|𝒢_{1/2} ∼ Bin(m,2t)` and `E[V(t)/t|𝒢_{1/2}] = 2m = V(1/2)/(1/2)`)
is a self-contained development of its own, mirroring `Knockoff/Supermartingale.lean`. The
integrability claim is the substantive analytic content (`V(τ)/τ` is unbounded near `τ → 0`; it is
integrable precisely because the reverse-MG keeps `E[V(t)/t] = 2n₀` constant). -/
theorem storey_reverseMG_ost (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) (q : ℝ)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    Integrable (storeyLHSint H₀ p q) μ ∧
      ∫ ω, storeyLHSint H₀ p q ω ∂μ = ∫ ω, storeyRHSint H₀ p ω ∂μ := by
  sorry

/-! ## Binomial law of the null-count `V(1/2)` (the missing piece of `storey_binom_bound`)

For an i.i.d. fair `Bool` family `σ : ι → Ω → Bool` (here `ι = {j // j ∈ H₀}`, `σ j = 𝟙(pⱼ ≤ 1/2)`),
the Hamming-weight law is `μ{ #{i : σ i} = k } = C(|ι|,k)·(1/2)^{|ι|}`. This is the type-vector
partition computation of `ForMathlib/SymmetricCondExp` (`measure_setOf_typeVec`), reproduced here
because that lemma is `private`. -/

open scoped Classical in
/-- Membership in `evtSet σ T`: the sample's true-coordinates are exactly `T`. -/
private lemma storey_mem_evtSet {ι : Type*} [Fintype ι] (σ : ι → Ω → Bool) (T : Finset ι) (ω : Ω) :
    ω ∈ evtSet σ T ↔ typeVec σ ω = T := by
  simp only [evtSet, Set.mem_iInter, Set.mem_preimage]
  rw [Finset.ext_iff]
  refine forall_congr' (fun i => ?_)
  simp only [typeVec, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i ∈ T <;> simp [hi, Set.mem_singleton_iff, Bool.not_eq_true]

private lemma storey_measurableSet_evtSet {ι : Type*} [Fintype ι] {σ : ι → Ω → Bool}
    (hσ : ∀ i, Measurable (σ i)) (T : Finset ι) : MeasurableSet (evtSet σ T) := by
  unfold evtSet
  refine MeasurableSet.iInter (fun i => ?_)
  exact hσ i MeasurableSet.of_discrete

open scoped Classical in
/-- Each cell of the type-vector partition has measure `(1/2)^|ι|` (independence + fairness). -/
private lemma storey_measure_evtSet {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {σ : ι → Ω → Bool} (hσ : ∀ i, Measurable (σ i))
    (hindep : iIndepFun σ μ) (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (T : Finset ι) :
    μ (evtSet σ T) = (1 / 2 : ℝ≥0∞) ^ (Fintype.card ι) := by
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
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ]

/-- **Master measure computation.** The measure of any event described by a property `Q` of the
type vector is `(#allowed type vectors)·(1/2)^{|ι|}`. -/
private lemma storey_measure_setOf_typeVec {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {σ : ι → Ω → Bool} (hσ : ∀ i, Measurable (σ i))
    (hindep : iIndepFun σ μ) (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2)
    (Q : Finset ι → Prop) [DecidablePred Q] :
    μ {ω | Q (typeVec σ ω)}
      = ((Finset.univ.powerset.filter Q).card) • (1 / 2 : ℝ≥0∞) ^ (Fintype.card ι) := by
  have hset : {ω | Q (typeVec σ ω)}
      = ⋃ T ∈ (Finset.univ.powerset.filter Q), evtSet σ T := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, storey_mem_evtSet, exists_prop]
    constructor
    · intro hQ; exact ⟨typeVec σ ω, hQ, rfl⟩
    · rintro ⟨T, hQT, rfl⟩; exact hQT
  have hdisj : (↑(Finset.univ.powerset.filter Q) : Set (Finset ι)).PairwiseDisjoint
      (evtSet σ) := by
    intro T _ T' _ hne
    change Disjoint (evtSet σ T) (evtSet σ T')
    rw [Set.disjoint_left]
    intro ω hω hω'
    exact hne (((storey_mem_evtSet σ T ω).mp hω).symm.trans ((storey_mem_evtSet σ T' ω).mp hω'))
  have hmeas : ∀ T ∈ Finset.univ.powerset.filter Q, MeasurableSet (evtSet σ T) :=
    fun T _ => storey_measurableSet_evtSet hσ T
  rw [hset, measure_biUnion_finset hdisj hmeas,
    Finset.sum_congr rfl (fun T _ => storey_measure_evtSet μ hσ hindep hfair T), Finset.sum_const]

/-- **Binomial Hamming-weight law.** `μ{ #{i : σ i = true} = k } = C(|ι|,k)·(1/2)^{|ι|}`. -/
private lemma storey_typeVec_card_law {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {σ : ι → Ω → Bool} (hσ : ∀ i, Measurable (σ i))
    (hindep : iIndepFun σ μ) (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (k : ℕ) :
    μ {ω | (typeVec σ ω).card = k}
      = ((Fintype.card ι).choose k : ℕ) • (1 / 2 : ℝ≥0∞) ^ (Fintype.card ι) := by
  rw [storey_measure_setOf_typeVec μ hσ hindep hfair (fun T => T.card = k)]
  congr 1
  rw [← Finset.card_univ (α := ι), ← Finset.card_powersetCard k (Finset.univ : Finset ι),
    Finset.powersetCard_eq_filter]

/-- **Binomial null-count bound** (Candès L7 §7.4): `∫ V(1/2)/(1+n₀−V(1/2)) ≤ 1`. For independent
uniform nulls, `V(1/2) ∼ Bin(n₀, 1/2)`, so the integral equals
`∑ₖ C(n₀,k)·2^{−n₀}·k/(1+(n₀−k)) = 1 − 2^{−n₀} ≤ 1` via `binom_ratio_sum_le_one`.

The law `V(1/2) ∼ Bin(n₀,1/2)` (`storey_typeVec_card_law`) turns the integral into that finite sum
by LOTUS over the finite range of `V`. -/
theorem storey_binom_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∫ ω, storeyRHSint H₀ p ω ∂μ ≤ 1 := by
  classical
  -- The null-indicator family `σ j = 𝟙(pⱼ ≤ 1/2)`, indexed by the nulls `ι = {j // j ∈ H₀}`.
  set V : Ω → ℕ := fun ω => nullCountLE H₀ p (1 / 2) ω with hVdef
  set σ : {j // j ∈ H₀} → Ω → Bool :=
    fun i => (fun x : ℝ => if x ≤ 1 / 2 then true else false) ∘ p i.val with hσdef
  have hbf : Measurable (fun x : ℝ => if x ≤ 1 / 2 then true else false) :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
      measurable_const
  have hσtrue : ∀ (i : {j // j ∈ H₀}) (ω : Ω), σ i ω = true ↔ p i.val ω ≤ 1 / 2 := by
    intro i ω
    simp only [hσdef, Function.comp_apply]
    by_cases hc : p i.val ω ≤ 1 / 2 <;> simp [hc]
  have hσmeas : ∀ i, Measurable (σ i) := fun i => hbf.comp (hmeas i.val)
  have hσindep : iIndepFun σ μ :=
    (hindep.precomp Subtype.val_injective).comp _ (fun _ => hbf)
  have hσfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2 := by
    intro i
    have hset : {ω | σ i ω = true} = {ω | p i.val ω ≤ 1 / 2} := by
      ext ω; simp only [Set.mem_setOf_eq, hσtrue i ω]
    rw [hset, hnull i.val i.property (1 / 2) (by norm_num) (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    simp
  -- `V ω = #{i : σ i ω = true} = (typeVec σ ω).card`, and `Fintype.card {j // j ∈ H₀} = H₀.card`.
  have hcard : Fintype.card {j // j ∈ H₀} = H₀.card := Fintype.card_coe H₀
  have hcount : ∀ ω, (typeVec σ ω).card = V ω := by
    intro ω
    simp only [hVdef, typeVec, nullCountLE]
    refine Finset.card_bij (fun i _ => (i : Fin n)) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_filter]
      exact ⟨i.property, (hσtrue i ω).mp hi⟩
    · intro a _ b _ hab; exact Subtype.ext hab
    · intro j hj
      simp only [Finset.mem_filter] at hj
      refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hσtrue ⟨j, hj.1⟩ ω).mpr hj.2
  -- The binomial law of `V`, transported to reals.
  have hsk : ∀ k, MeasurableSet {ω | V ω = k} := by
    intro k
    exact measurable_nullCountLE H₀ p hmeas (1 / 2) (measurableSet_singleton k)
  have hlaw_real : ∀ k, (μ {ω | V ω = k}).toReal
      = (H₀.card.choose k : ℝ) / 2 ^ H₀.card := by
    intro k
    have hset : {ω | V ω = k} = {ω | (typeVec σ ω).card = k} := by
      ext ω; simp only [Set.mem_setOf_eq, hcount ω]
    rw [hset, storey_typeVec_card_law μ hσmeas hσindep hσfair k, hcard,
      nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
    have h12 : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
      rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]; norm_num
    rw [h12, div_pow, one_pow, mul_one_div]
  -- LOTUS: `storeyRHSint ω = h(V ω)` and `h(V ω) = ∑_{k≤n₀} 𝟙(V=k)·h(k)`.
  have hVle : ∀ ω, V ω ≤ H₀.card := fun ω => nullCountLE_le_card H₀ p (1 / 2) ω
  have hpt : ∀ ω, storeyRHSint H₀ p ω
      = ∑ k ∈ Finset.range (H₀.card + 1),
          (if V ω = k then (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))) else 0) := by
    intro ω
    rw [Finset.sum_ite_eq (Finset.range (H₀.card + 1)) (V ω)
      (fun k => (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))))]
    rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (hVle ω)))]
    simp only [storeyRHSint, storeyDenom, hVdef]
    ring
  have hterm : ∀ k, ∫ ω, (if V ω = k then (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))) else 0) ∂μ
      = (μ {ω | V ω = k}).toReal * ((k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ)))) := by
    intro k
    have hind : (fun ω => if V ω = k then (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))) else 0)
        = {ω | V ω = k}.indicator (fun _ => (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ)))) := by
      funext ω; rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]
    rw [hind, integral_indicator_const _ (hsk k), measureReal_def, smul_eq_mul]
  calc ∫ ω, storeyRHSint H₀ p ω ∂μ
      = ∫ ω, (∑ k ∈ Finset.range (H₀.card + 1),
          (if V ω = k then (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))) else 0)) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ k ∈ Finset.range (H₀.card + 1),
          ∫ ω, (if V ω = k then (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))) else 0) ∂μ := by
        refine integral_finset_sum _ (fun k _ => ?_)
        have hind : (fun ω => if V ω = k then (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ))) else 0)
            = {ω | V ω = k}.indicator (fun _ => (k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ)))) := by
          funext ω; rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]
        rw [hind]
        exact (integrable_const _).indicator (hsk k)
    _ = ∑ k ∈ Finset.range (H₀.card + 1),
          (H₀.card.choose k : ℝ) / 2 ^ H₀.card * ((k : ℝ) / (1 + ((H₀.card : ℝ) - (k : ℝ)))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hterm k, hlaw_real k]
    _ ≤ 1 := binom_ratio_sum_le_one H₀.card

/-! ## Rewriting the Storey FDP into the counting-process form

The rejection set `storeyRejects p q ω = {i : pᵢ(ω) ≤ τ}` (with `τ = storeyThreshold p q ω`) makes
the rejection / false-rejection counts coincide with the threshold counting processes at `t = τ`:
`numRejections = R(τ) = countLE p τ` and `numFalseRejections = V(τ) = nullCountLE H₀ p τ`. Hence
`FDP = V(τ)/(R(τ)∨1)`. These are pure `Finset` rewrites (no probability) and are the bridge between
the `FDP/Defs` layer and the `EmpiricalCDF` counting processes that the martingale argument runs on.
-/

/-- The Storey rejection set intersected with the nulls is exactly the null counting filter at
`t = τ`: `{i : pᵢ ≤ τ} ∩ H₀ = {j ∈ H₀ : pⱼ ≤ τ}`. -/
private lemma storeyRejects_inter_eq (p : Fin n → Ω → ℝ) (q : ℝ) (H₀ : Finset (Fin n)) (ω : Ω) :
    storeyRejects p q ω ∩ H₀
      = H₀.filter (fun j => p j ω ≤ storeyThreshold p q ω) := by
  ext j
  simp only [storeyRejects, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- `numRejections (storeyRejects p q) = R(τ) = countLE p τ` (`τ = storeyThreshold p q ω`). -/
private lemma storey_numRejections_eq (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) :
    numRejections (storeyRejects p q) ω = countLE p (storeyThreshold p q ω) ω := rfl

/-- `numFalseRejections H₀ (storeyRejects p q) = V(τ) = nullCountLE H₀ p τ`. -/
private lemma storey_numFalseRejections_eq (p : Fin n → Ω → ℝ) (q : ℝ) (H₀ : Finset (Fin n))
    (ω : Ω) :
    numFalseRejections H₀ (storeyRejects p q) ω
      = nullCountLE H₀ p (storeyThreshold p q ω) ω := by
  unfold numFalseRejections nullCountLE
  rw [storeyRejects_inter_eq]

/-- The Storey FDP in counting-process form: `FDP = V(τ)/(R(τ)∨1)`. -/
private lemma storey_FDP_eq (p : Fin n → Ω → ℝ) (q : ℝ) (H₀ : Finset (Fin n)) (ω : Ω) :
    FDP H₀ (storeyRejects p q) ω
      = (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
          / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 := by
  unfold FDP
  rw [storey_numFalseRejections_eq, storey_numRejections_eq]

/-! ## Threshold attainment and the pointwise FDP bound -/

private lemma storeyFDRhat_zero (p : Fin n → Ω → ℝ) (ω : Ω) :
    storeyFDRhat p 0 ω = 0 := by
  simp [storeyFDRhat]

private lemma storeyThreshold_set_bddAbove (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) :
    BddAbove {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q} :=
  ⟨1 / 2, fun t ht => ht.1.2⟩

private lemma storeyThreshold_zero_mem (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    (0 : ℝ) ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q} :=
  ⟨⟨le_rfl, by norm_num⟩, by rw [storeyFDRhat_zero]; exact hq0.le⟩

private lemma storeyThreshold_nonneg (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    0 ≤ storeyThreshold p q ω :=
  le_csSup (storeyThreshold_set_bddAbove p q ω) (storeyThreshold_zero_mem p hq0 ω)

/-- **Threshold attainment** (the right-continuity ingredient of Theorem 3): the estimated FDR at
the data-dependent threshold `τ = storeyThreshold p q ω` does not exceed `q`. `storeyFDRhat p · ω`
is right-continuous in `t` (continuous numerator `π̂₀·n·t` over the right-continuous step
denominator `R(·)∨1`); at the `sSup`, either `τ` is not an order statistic (continuity gives the
left-limit `≤ q`) or `R(·)` jumps up at `τ` (so the value drops below the left-limit `≤ q`). Either
way `≤ q`.

The sublevel set is in fact closed, but rather than topology we argue by monotonicity of `countLE`:
if `g(τ) = π̂₀·n·τ/(R(τ)∨1) > q` then, because `R(·)` is monotone, every `s ∈ (a, τ]` with
`a = q·(R(τ)∨1)/(π̂₀·n)` has `g(s) ≥ π̂₀·n·s/(R(τ)∨1) > q`, so `a` would be a strictly smaller upper
bound of the sublevel set than its supremum `τ` — contradiction. -/
private theorem storey_threshold_attained (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    storeyFDRhat p (storeyThreshold p q ω) ω ≤ q := by
  set S := {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q} with hS
  set τ := storeyThreshold p q ω with hτdef
  have hbdd : BddAbove S := storeyThreshold_set_bddAbove p q ω
  have hne : S.Nonempty := ⟨0, storeyThreshold_zero_mem p hq0 ω⟩
  have hτnn : 0 ≤ τ := storeyThreshold_nonneg p hq0 ω
  by_contra hcon
  rw [not_le] at hcon
  set C := storeyPiZero p ω * (n : ℝ) with hC
  have hMpos : ∀ t : ℝ, (0 : ℝ) < max (countLE p t ω : ℝ) 1 :=
    fun t => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hgτ : storeyFDRhat p τ ω = C * τ / max (countLE p τ ω : ℝ) 1 := rfl
  rw [hgτ, lt_div_iff₀ (hMpos τ)] at hcon
  have hqM : 0 < q * max (countLE p τ ω : ℝ) 1 := mul_pos hq0 (hMpos τ)
  have hCτpos : 0 < C * τ := lt_trans hqM hcon
  have hτpos : 0 < τ := by
    rcases lt_or_eq_of_le hτnn with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hCτpos; exact lt_irrefl _ hCτpos
  have hCpos : 0 < C := by nlinarith [hCτpos, hτpos]
  set a := q * max (countLE p τ ω : ℝ) 1 / C with ha
  have haτ : a < τ := by rw [ha, div_lt_iff₀ hCpos]; nlinarith [hcon]
  have hapos : 0 < a := by rw [ha]; positivity
  have hub : ∀ s ∈ S, s ≤ a := by
    intro s hs
    by_contra hsa
    rw [not_le] at hsa
    have hsτ : s ≤ τ := le_csSup hbdd hs
    have hRs : (countLE p s ω : ℝ) ≤ (countLE p τ ω : ℝ) := by
      exact_mod_cast countLE_mono p ω hsτ
    have hden : max (countLE p s ω : ℝ) 1 ≤ max (countLE p τ ω : ℝ) 1 := by
      gcongr
    have hsnn : 0 ≤ s := le_of_lt (lt_trans hapos hsa)
    have hCsnn : 0 ≤ C * s := mul_nonneg hCpos.le hsnn
    rw [ha, div_lt_iff₀ hCpos] at hsa
    have hchain : q < storeyFDRhat p s ω := by
      have hgs : storeyFDRhat p s ω = C * s / max (countLE p s ω : ℝ) 1 := rfl
      rw [hgs]
      refine lt_of_lt_of_le ?_ (div_le_div_of_nonneg_left hCsnn (hMpos s) hden)
      rw [lt_div_iff₀ (hMpos τ)]
      nlinarith [hsa]
    exact absurd hs.2 (not_le.mpr hchain)
  have hτa : τ ≤ a := csSup_le hne hub
  linarith [haτ]

/-- Splitting the rejection count over nulls and non-nulls: `R(t) + n₀ ≤ V(t) + n` (`n₀ = H₀.card`).
The non-null rejections `R(t) − V(t) = #{j ∉ H₀ : pⱼ ≤ t}` are at most the `n − n₀` non-nulls. -/
private lemma countLE_add_card_le (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    countLE p t ω + H₀.card ≤ nullCountLE H₀ p t ω + n := by
  classical
  set P : Fin n → Prop := fun j => p j ω ≤ t with hP
  have hcount : countLE p t ω
      = (H₀.filter P).card + (H₀ᶜ.filter P).card := by
    unfold countLE
    rw [← Finset.card_filter_add_card_filter_not (p := fun j => j ∈ H₀)]
    congr 1
    · rw [Finset.filter_filter]; congr 1; ext j; simp [hP, and_comm]
    · rw [Finset.filter_filter]; congr 1; ext j; simp [hP, and_comm, Finset.mem_compl]
  have hnn : (H₀ᶜ.filter P).card ≤ n - H₀.card := by
    calc (H₀ᶜ.filter P).card ≤ H₀ᶜ.card := Finset.card_filter_le _ _
      _ = n - H₀.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hcard : H₀.card ≤ n := by simpa using Finset.card_le_univ H₀
  rw [hcount]
  have : (H₀.filter P).card = nullCountLE H₀ p t ω := rfl
  omega

/-- a.e. every null p-value is strictly positive: `μ{ω | pⱼ ω ≤ 0} = ofReal 0 = 0` for `j ∈ H₀`. -/
private lemma storey_nulls_pos (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ)
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∀ᵐ ω ∂μ, ∀ j ∈ H₀, 0 < p j ω := by
  rw [Filter.eventually_all_finset]
  intro j hj
  have h0 : μ {ω | p j ω ≤ 0} = 0 := by
    rw [hnull j hj 0 le_rfl (by norm_num)]; simp
  rw [ae_iff]
  convert h0 using 2
  ext ω; simp [not_lt]

/-- The real-arithmetic core of the pointwise FDP bound: from the threshold attainment
`c·τ ≤ q·MR` and `2·den ≤ c` (with `MR, den, τ > 0`, `V ≥ 0`), conclude
`V/MR ≤ q·(V/τ)·(1/2)/den`. Here `c = π̂₀·n`, `MR = R(τ)∨1`, `den = 1+n₀−V(1/2)`. -/
private lemma storey_arith (V MR den τ q c : ℝ)
    (hV : 0 ≤ V) (hMR : 0 < MR) (hden : 0 < den) (hτ : 0 < τ)
    (hc2 : 2 * den ≤ c) (hatt : c * τ ≤ q * MR) :
    V / MR ≤ q * (V / τ * (1 / 2 / den)) := by
  have h2 : 2 * den * τ ≤ q * MR := le_trans (mul_le_mul_of_nonneg_right hc2 hτ.le) hatt
  have hkey : V * (2 * den * τ) ≤ q * V * MR := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hV]
  rw [div_le_iff₀ hMR]
  have hRHS : q * (V / τ * (1 / 2 / den)) * MR = q * V * MR / (2 * den * τ) := by
    field_simp [hτ.ne', hden.ne']
  rw [hRHS, le_div_iff₀ (by positivity)]
  exact hkey

/-- **Pointwise FDP bound** (threshold attainment, in counting-process form): a.e.,
`V(τ)/(R(τ)∨1) ≤ q · (V(τ)/τ) · (1/2)/(1+n₀−V(1/2))`. The `τ = 0` branch uses
`storey_nulls_pos` (then `V(0) = 0`); the `τ > 0` branch combines `storey_threshold_attained`
(`π̂₀·n·τ ≤ q·(R(τ)∨1)`) with `π̂₀·n = 2(1+n−R(1/2)) ≥ 2·(1+n₀−V(1/2))` (`countLE_add_card_le`). -/
private lemma storey_FDP_le_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∀ᵐ ω ∂μ, (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
        / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1
      ≤ q * storeyLHSint H₀ p q ω := by
  filter_upwards [storey_nulls_pos μ H₀ p hnull] with ω hpos
  simp only [storeyLHSint]
  have hMR0 : (0 : ℝ) < max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 :=
    lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden0 : 0 < storeyDenom H₀ p ω := storeyDenom_pos H₀ p ω
  have hτnn : 0 ≤ storeyThreshold p q ω := storeyThreshold_nonneg p hq0 ω
  by_cases hVz : nullCountLE H₀ p (storeyThreshold p q ω) ω = 0
  · rw [hVz]; simp
  · -- V(τ) > 0
    have hVpos : (0 : ℝ) < (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ) := by
      have := Nat.pos_of_ne_zero hVz; exact_mod_cast this
    -- V(τ) > 0 forces n > 0
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact absurd (by simp [Finset.eq_empty_of_isEmpty H₀, nullCountLE]) hVz
      · exact h
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    -- τ > 0 (else V(τ)=V(0)=0 by nulls positive)
    rcases eq_or_lt_of_le hτnn with hτ0 | hτpos
    · exfalso
      apply hVz
      have h0 : nullCountLE H₀ p 0 ω = 0 := by
        unfold nullCountLE
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj; exact not_le.mpr (hpos j hj)
      rw [← hτ0]; exact h0
    · -- main branch: apply the arithmetic core
      set c : ℝ := storeyPiZero p ω * (n : ℝ) with hcdef
      have hc_eq : c = 2 * (1 + (n : ℝ) - (countLE p (1 / 2) ω : ℝ)) := by
        rw [hcdef]; unfold storeyPiZero; field_simp
      have hcast : (countLE p (1 / 2) ω : ℝ) + (H₀.card : ℝ)
          ≤ (nullCountLE H₀ p (1 / 2) ω : ℝ) + (n : ℝ) := by
        exact_mod_cast countLE_add_card_le H₀ p (1 / 2) ω
      have hc2 : 2 * storeyDenom H₀ p ω ≤ c := by
        rw [hc_eq]; unfold storeyDenom; linarith
      have hatt0 := storey_threshold_attained p hq0 ω
      simp only [storeyFDRhat] at hatt0
      rw [div_le_iff₀ hMR0] at hatt0
      have hatt : c * storeyThreshold p q ω
          ≤ q * max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 := by
        rw [hcdef]; exact hatt0
      exact storey_arith _ _ _ _ q c hVpos.le hMR0 hden0 hτpos hc2 hatt

/-- **Storey's procedure controls FDR** (Candès, Lecture 7, §7.4, Theorem 3, STAT 300C). For
independent uniform null p-values, `FDR ≤ q`.

The full assembly is verified here from three sharp named bricks isolating the irreducible
probabilistic content: `storey_reverseMG_ost` (the reverse-martingale optional-stopping identity,
`∫ (V(τ)/τ)·w = ∫ V(1/2)/(1+n₀−V(1/2))`, with integrability), `storey_binom_bound` (the binomial
null-count law `∫ V(1/2)/(1+n₀−V(1/2)) ≤ 1`), and `storey_threshold_attained` (the right-continuity
attainment `storeyFDRhat τ ≤ q`, consumed via the proved pointwise bound `storey_FDP_le_bound`).
Reducing `FDR = E[FDP]` to `E[FDP] ≤ q·∫ LHS = q·∫ RHS ≤ q` is the proved glue. -/
theorem storey_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    FDR H₀ (storeyRejects p q) μ ≤ q := by
  -- Reduce `FDR = E[FDP]` to the counting-process form `E[ V(τ)/(R(τ)∨1) ]`.
  rw [FDR]
  simp_rw [storey_FDP_eq]
  obtain ⟨hLint, hOST⟩ := storey_reverseMG_ost μ H₀ p q hmeas hindep hnull
  have hg_int : Integrable (fun ω => q * storeyLHSint H₀ p q ω) μ := hLint.const_mul q
  have hfdp_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω =>
      (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
        / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 := by
    filter_upwards with ω
    exact div_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (le_max_right _ _))
  calc ∫ ω, (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
          / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 ∂μ
      ≤ ∫ ω, q * storeyLHSint H₀ p q ω ∂μ :=
        integral_mono_of_nonneg hfdp_nonneg hg_int
          (storey_FDP_le_bound μ H₀ p hq0 hnull)
    _ = q * ∫ ω, storeyLHSint H₀ p q ω ∂μ := integral_const_mul q _
    _ = q * ∫ ω, storeyRHSint H₀ p ω ∂μ := by rw [hOST]
    _ ≤ q * 1 :=
        mul_le_mul_of_nonneg_left (storey_binom_bound μ H₀ p hmeas hindep hnull) hq0.le
    _ = q := mul_one q

end StatLean.MultipleTesting
