import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.CondCharFun
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Brown/Hall–Heyde martingale central limit theorem

**Main theorem** (`mds_clt`): a martingale-difference triangular array whose
conditional variance process converges in probability to a constant `σ²` and which
satisfies the (unconditional) Lindeberg condition has asymptotically `N(0, σ²)` row
sums — stated through pointwise characteristic-function convergence.

This is the probability pillar commissioned for Hannan's Theorem 3.2 (FY §3.2): the
ARMA quasi-score at the true parameter is a stationary ergodic martingale-difference
sequence, and the array `X_{n,i} = ξ_i/√n` fed into `mds_clt` yields asymptotic
normality of the score (batch D wires this through `ARMA/ScoreAnalysis`).

**Assembly plan** (from `MartingaleCLT/CondCharFun.lean`):
1. `norm_integral_exp_rowSum_sub_prod_le` reduces `E e^{iuS_n}` to the Taylor product
   at cost of the Lindeberg sums (choose `ε = ε_n → 0` slowly);
2. `tendsto_integral_prod_one_sub_condVar` sends the Taylor product to `e^{−u²σ²/2}`
   (uniform negligibility of the conditional variances follows from Lindeberg +
   variance convergence — derive, don't assume);
3. rewrite `charFun (gaussianReal 0 σ²) u = e^{−u²σ²/2}`.
The truncation/stopping refinement of Hall–Heyde (replacing the L¹-boundedness input
by a stopping-time argument) is NOT needed at this generality: the `hbdd` input of
step 2 is derived from `hvar` + `hlind` via the row variance identity
`Σᵢ E Xᵢ² = E V_n`.

**Reference.** B. M. Brown, *Martingale central limit theorems*, Ann. Math. Statist.
**42** (1971), 59–66, Thm 2; P. Hall & C. C. Heyde, *Martingale Limit Theory and Its
Application*, Academic Press, 1980, Thm 3.2/Cor 3.1. (`Hall–Heyde Thm 3.2`.)

**Bibliographic comments.** Martingale CLTs originate with P. Lévy (1935, 1937);
Billingsley (1961) and Ibragimov (1963) proved the stationary-ergodic case; Brown
(1971) isolated the conditional-variance normalization; Hall–Heyde (1980) is the
standard reference form. The charFun proof implemented here is Brown's original
telescope, with the conditional Taylor estimates of `CondCharFun.lean`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Truncation

/-!
### The truncated array

The `hbdd` input of `tendsto_integral_prod_one_sub_condVar` (a uniform `L¹` bound on the
conditional variance process) is **not** a consequence of `hvar` + `hlind`: the variance
process may carry a vanishing-probability excursion of diverging expectation while both
Brown conditions hold.  We therefore run the classical Hall–Heyde truncation *inside*
`mds_clt`: the array is stopped at the first index at which the accumulated conditional
variance would exceed `σ² + 1`, which makes the truncated variance process bounded by
`σ² + 1` pointwise, hence `hbdd` trivial, and changes the row sum only on the event
`{V_n > σ² + 1}`, whose probability vanishes by `hvar`.
-/

variable {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
  {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}

/-- The `i`-th conditional variance `E[X_{n,i}² | 𝓕_{n,i}]` of the row `n`. -/
private noncomputable def cvar (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (n : ℕ)
    (i : Fin (k n)) : Ω → ℝ :=
  μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc]

private lemma mdsCondVariance_eq_sum_cvar (n : ℕ) (ω : Ω) :
    mdsCondVariance k X F μ n ω = ∑ i, cvar k X F μ n i ω := rfl

private lemma cvar_measurable (n : ℕ) (i : Fin (k n)) :
    Measurable[F n i.castSucc] (cvar k X F μ n i) :=
  stronglyMeasurable_condExp.measurable

private lemma cvar_measurable_le (h : IsMDSArray k X F μ) (n : ℕ) {i j : Fin (k n)} (hij : j ≤ i) :
    Measurable[F n i.castSucc] (cvar k X F μ n j) :=
  (cvar_measurable n j).mono (h.mono n (Fin.castSucc_le_castSucc_iff.2 hij)) le_rfl

private lemma cvar_nonneg (n : ℕ) (i : Fin (k n)) : 0 ≤ᵐ[μ] cvar k X F μ n i :=
  condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)

private lemma measurable_of_mds (h : IsMDSArray k X F μ) (n : ℕ) (i : Fin (k n)) :
    Measurable (X n i) := (h.adapted n i).mono (h.le_ambient n _) le_rfl

private lemma integrable_of_mds [IsFiniteMeasure μ] (h : IsMDSArray k X F μ) (n : ℕ)
    (i : Fin (k n)) : Integrable (X n i) μ := (h.memLp n i).integrable one_le_two

private lemma integrable_sq_of_mds (h : IsMDSArray k X F μ) (n : ℕ) (i : Fin (k n)) :
    Integrable (fun ω => X n i ω ^ 2) μ := (h.memLp n i).integrable_sq

private lemma integrable_mdsCondVariance : Integrable (mdsCondVariance k X F μ n) μ :=
  integrable_finset_sum _ fun _ _ => integrable_condExp

/-- The stopping set: the conditional variance accumulated **up to and including** `i` has
not yet exceeded the level `c`. -/
private def truncSet (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (c : ℝ) (n : ℕ)
    (i : Fin (k n)) : Set Ω :=
  {ω | ∑ j ∈ Finset.Iic i, cvar k X F μ n j ω ≤ c}

/-- The truncated array: the differences are switched off from the first index at which the
accumulated conditional variance would exceed `c`. -/
private noncomputable def truncArray (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (c : ℝ) (n : ℕ)
    (i : Fin (k n)) : Ω → ℝ :=
  (truncSet k X F μ c n i).indicator (X n i)

private lemma measurableSet_truncSet (h : IsMDSArray k X F μ) (c : ℝ) (n : ℕ) (i : Fin (k n)) :
    MeasurableSet[F n i.castSucc] (truncSet k X F μ c n i) :=
  measurableSet_le
    (Finset.measurable_sum _ fun j hj => cvar_measurable_le h n (Finset.mem_Iic.1 hj))
    measurable_const

private lemma isMDSArray_truncArray [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ) (c : ℝ) :
    IsMDSArray k (truncArray k X F μ c) F μ where
  le_ambient := h.le_ambient
  mono := h.mono
  adapted := fun n i =>
    (h.adapted n i).indicator
      (h.mono n (Fin.castSucc_le_succ i) _ (measurableSet_truncSet h c n i))
  memLp := fun n i =>
    (h.memLp n i).indicator (h.le_ambient n _ _ (measurableSet_truncSet h c n i))
  condexp_zero := fun n i => by
    have h1 := condExp_indicator (m := F n i.castSucc) (integrable_of_mds h n i)
      (measurableSet_truncSet h c n i)
    filter_upwards [h1, h.condexp_zero n i] with ω e1 e2
    show μ[(truncSet k X F μ c n i).indicator (X n i) | F n i.castSucc] ω = (0 : Ω → ℝ) ω
    rw [e1]
    by_cases hω : ω ∈ truncSet k X F μ c n i
    · simp [Set.indicator_of_mem hω, e2]
    · simp [Set.indicator_of_notMem hω]

private lemma cvar_truncArray (h : IsMDSArray k X F μ) (c : ℝ) (n : ℕ) (i : Fin (k n)) :
    cvar k (truncArray k X F μ c) F μ n i
      =ᵐ[μ] (truncSet k X F μ c n i).indicator (cvar k X F μ n i) := by
  have hsq : (fun ω => truncArray k X F μ c n i ω ^ 2)
      = (truncSet k X F μ c n i).indicator (fun ω => X n i ω ^ 2) := by
    funext ω; by_cases hω : ω ∈ truncSet k X F μ c n i <;>
      simp [truncArray, Set.indicator_apply, hω]
  show μ[fun ω => truncArray k X F μ c n i ω ^ 2 | F n i.castSucc] =ᵐ[μ] _
  rw [hsq]
  exact condExp_indicator (integrable_sq_of_mds h n i) (measurableSet_truncSet h c n i)

/-- The truncated conditional variance process never exceeds the truncation level. -/
private lemma mdsCondVariance_truncArray_le (h : IsMDSArray k X F μ) {c : ℝ} (hc : 0 ≤ c)
    (n : ℕ) : ∀ᵐ ω ∂μ, mdsCondVariance k (truncArray k X F μ c) F μ n ω ≤ c := by
  have hnn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ cvar k X F μ n i ω :=
    ae_all_iff.2 fun i => cvar_nonneg (μ := μ) n i
  have hc' : ∀ᵐ ω ∂μ, ∀ i, cvar k (truncArray k X F μ c) F μ n i ω
      = (truncSet k X F μ c n i).indicator (cvar k X F μ n i) ω :=
    ae_all_iff.2 fun i => cvar_truncArray h c n i
  filter_upwards [hnn, hc'] with ω hω hωc
  classical
  rw [mdsCondVariance_eq_sum_cvar]
  have hstep : ∀ i : Fin (k n), cvar k (truncArray k X F μ c) F μ n i ω
      = if i ∈ Finset.univ.filter (fun i => ω ∈ truncSet k X F μ c n i) then
          cvar k X F μ n i ω else 0 := by
    intro i
    rw [hωc i]
    by_cases hi : ω ∈ truncSet k X F μ c n i <;> simp [Set.indicator_apply, hi]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_ite_mem, Finset.univ_inter]
  set T : Finset (Fin (k n)) := Finset.univ.filter (fun i => ω ∈ truncSet k X F μ c n i) with hT
  rcases T.eq_empty_or_nonempty with he | hne
  · simpa [he] using hc
  · have hsub : T ⊆ Finset.Iic (T.max' hne) := fun j hj =>
      Finset.mem_Iic.2 (Finset.le_max' T j hj)
    have hmem : ω ∈ truncSet k X F μ c n (T.max' hne) :=
      (Finset.mem_filter.1 (T.max'_mem hne)).2
    calc ∑ i ∈ T, cvar k X F μ n i ω
        ≤ ∑ i ∈ Finset.Iic (T.max' hne), cvar k X F μ n i ω :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hω j
      _ ≤ c := hmem

/-- Conditional monotonicity against a constant shift. -/
private lemma condExp_le_const_add {α : Type*} {m mα : MeasurableSpace α} {ν : Measure α}
    [IsFiniteMeasure ν] (hm : m ≤ mα) {f g : α → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    {c : ℝ} (hfg : ∀ᵐ ω ∂ν, f ω ≤ c + g ω) :
    ∀ᵐ ω ∂ν, ν[f | m] ω ≤ c + ν[g | m] ω := by
  have h1 : ν[f | m] ≤ᵐ[ν] ν[fun ω => c + g ω | m] :=
    condExp_mono hf ((integrable_const c).add hg) hfg
  have h2 : ν[fun ω => c + g ω | m] =ᵐ[ν] ν[fun _ : α => c | m] + ν[g | m] :=
    condExp_add (integrable_const c) hg m
  filter_upwards [h1, h2] with ω e1 e2
  have e3 : ν[fun _ : α => c | m] ω = c := by rw [condExp_const (μ := ν) hm c]
  calc ν[f | m] ω ≤ ν[fun ω => c + g ω | m] ω := e1
    _ = ν[fun _ : α => c | m] ω + ν[g | m] ω := e2
    _ = c + ν[g | m] ω := by rw [e3]

/-- **Uniform asymptotic negligibility of the conditional variances** is a consequence of the
(unconditional) Lindeberg condition: `E[X²|𝓕] ≤ ε² + E[X²1_{|X| ≥ ε}|𝓕]`, and the sum of the
latter has vanishing expectation, so Markov's inequality applies. -/
private lemma tendsto_measure_exists_cvar_ge [IsProbabilityMeasure μ] (h : IsMDSArray k X F μ)
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω}).toReal) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 = δ / 2 :=
    ⟨Real.sqrt (δ / 2), Real.sqrt_pos.2 (by linarith), Real.sq_sqrt (by linarith)⟩
  have hmeasS : ∀ (n : ℕ) (i : Fin (k n)), MeasurableSet {x : Ω | ε ≤ |X n i x|} := fun n i =>
    measurableSet_le measurable_const (measurable_of_mds h n i).abs
  set Y : (n : ℕ) → (i : Fin (k n)) → Ω → ℝ := fun n i =>
    Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω' => X n i ω' ^ 2) with hYdef
  have hYint : ∀ (n : ℕ) (i : Fin (k n)), Integrable (Y n i) μ := fun n i =>
    (integrable_sq_of_mds h n i).indicator (hmeasS n i)
  have hYnn : ∀ (n : ℕ) (i : Fin (k n)), 0 ≤ᵐ[μ] Y n i := fun n i =>
    ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  set Z : ℕ → Ω → ℝ := fun n ω => ∑ i, μ[Y n i | F n i.castSucc] ω with hZdef
  have hZint : ∀ n, Integrable (Z n) μ := fun n =>
    integrable_finset_sum _ fun _ _ => integrable_condExp
  have hZnn : ∀ n, 0 ≤ᵐ[μ] Z n := fun n => by
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (k n), 0 ≤ μ[Y n i | F n i.castSucc] ω :=
      ae_all_iff.2 fun i => condExp_nonneg (hYnn n i)
    filter_upwards [hall] with ω hω
    exact Finset.sum_nonneg fun i _ => hω i
  have hZmean : ∀ n, ∫ ω, Z n ω ∂μ = ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂μ := by
    intro n
    rw [hZdef]
    rw [integral_finset_sum _ fun (i : Fin (k n)) _ =>
      (integrable_condExp : Integrable (μ[Y n i | F n i.castSucc]) μ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_condExp (h.le_ambient n i.castSucc), hYdef, integral_indicator (hmeasS n i)]
  have hincl : ∀ n, μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω} ≤ μ {ω | δ / 2 ≤ Z n ω} := by
    intro n
    refine measure_mono_ae ?_
    have hkey : ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
        cvar k X F μ n i ω ≤ ε ^ 2 + μ[Y n i | F n i.castSucc] ω := by
      refine ae_all_iff.2 fun i => ?_
      refine condExp_le_const_add (h.le_ambient n i.castSucc) (integrable_sq_of_mds h n i)
        (hYint n i) (ae_of_all _ fun ω => ?_)
      by_cases hω : ω ∈ {x : Ω | ε ≤ |X n i x|}
      · have hY : Y n i ω = X n i ω ^ 2 := by
          show Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω' => X n i ω' ^ 2) ω = _
          exact Set.indicator_of_mem hω _
        rw [hY]; nlinarith [sq_nonneg ε]
      · have hY : Y n i ω = 0 := by
          show Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω' => X n i ω' ^ 2) ω = 0
          exact Set.indicator_of_notMem hω _
        have hlt : |X n i ω| < ε := lt_of_not_ge hω
        rw [hY, add_zero]
        nlinarith [abs_nonneg (X n i ω), sq_abs (X n i ω)]
    have hnn : ∀ᵐ ω ∂μ, ∀ i : Fin (k n), 0 ≤ μ[Y n i | F n i.castSucc] ω :=
      ae_all_iff.2 fun i => condExp_nonneg (hYnn n i)
    filter_upwards [hkey, hnn] with ω e1 e2 hmem
    obtain ⟨i, hi⟩ := hmem
    have hhalf : δ / 2 ≤ μ[Y n i | F n i.castSucc] ω := by
      have := e1 i; rw [hε2] at this; linarith
    exact hhalf.trans (Finset.single_le_sum
      (f := fun j => μ[Y n j | F n j.castSucc] ω) (fun j _ => e2 j) (Finset.mem_univ i))
  have hg : Tendsto (fun n => 2 / δ * ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂μ)
      atTop (𝓝 0) := by simpa using (hlind ε hε).const_mul (2 / δ)
  refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hg
  have hmark := mul_meas_ge_le_integral_of_nonneg (hZnn n) (hZint n) (δ / 2)
  rw [hZmean n] at hmark
  have h1 : (μ {ω | ∃ i, δ ≤ cvar k X F μ n i ω}).toReal ≤ μ.real {ω | δ / 2 ≤ Z n ω} := by
    rw [measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (hincl n)
  refine h1.trans ?_
  have hc : (0 : ℝ) < 2 / δ := by positivity
  calc μ.real {ω | δ / 2 ≤ Z n ω}
      = 2 / δ * (δ / 2 * μ.real {ω | δ / 2 ≤ Z n ω}) := by field_simp
    _ ≤ 2 / δ * ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_left hmark hc.le

end Truncation

/-- **The Brown/Hall–Heyde martingale CLT** (charFun form): martingale-difference
array + conditional variance `→p σ²` + Lindeberg ⇒ row sums are asymptotically
`N(0, σ²)`. -/
theorem mds_clt [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: conditional variance → σ² in probability; Brown's condition
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: the Lindeberg condition; Hall–Heyde (3.7) unconditional form
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map (mdsRowSum k X n)) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

/-- **Stationary-sequence corollary** (the Hannan-facing form): a single
martingale-difference sequence `ξ` against a filtration `G` with
`n⁻¹ Σ_{i<n} E[ξᵢ² | Gᵢ] →p σ²` and the averaged Lindeberg property has
`S_n/√n →d N(0, σ²)`. Instantiates `mds_clt` at `X_{n,i} = ξ_i/√n`. -/
theorem mds_clt_sequence [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → ℝ} {G : ℕ → MeasurableSpace Ω}
    (hle : ∀ i, G i ≤ ‹MeasurableSpace Ω›) (hmono : Monotone G)
    (hadapted : ∀ i, Measurable[G (i + 1)] (ξ i))
    (hL2 : ∀ i, MemLp (ξ i) 2 μ)
    -- USER-INPUT: martingale-difference property; Hall–Heyde Thm 3.2 setting
    (hmds : ∀ i, μ[ξ i | G i] =ᵐ[μ] 0)
    {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: averaged conditional variance → σ² in probability
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
          (∑ i ∈ Finset.range n, μ[fun ω' => ξ i ω' ^ 2 | G i] ω) - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: averaged Lindeberg condition
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ i ω|}, (ξ i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ξ i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

end StatLean.TimeSeries
