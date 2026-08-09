import StatLean.TimeSeries.ARMA.Consistency
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
import StatLean.TimeSeries.Process.SampleACF

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries
namespace S12b

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Noise

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

private lemma memLp_noise (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) : MemLp (ε t) 2 μ :=
  ((hiid.identDistrib t 0).memLp_iff).2 hiid.memLp

private lemma integral_noise (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) : ∫ ω, ε t ω ∂μ = 0 := by
  rw [(hiid.identDistrib t 0).integral_eq]; exact hiid.integral_eq_zero

private lemma integral_noise_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) :
    ∫ ω, ε t ω ^ 2 ∂μ = σ2 := by
  have hv : variance (ε t) μ = σ2 := by
    rw [(hiid.identDistrib t 0).variance_eq]; exact hiid.variance_eq
  have h := variance_eq_sub (memLp_noise hiid t)
  rw [hv, integral_noise hiid t] at h
  simpa using h.symm

end Noise

section MDS

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- The lag-`k` innovation product `ξ_i = ε_{i+1} ε_{i+1+k}`, the martingale difference
carrying the sample-ACF numerator. -/
private noncomputable def acfProd (ε : ℤ → Ω → ℝ) (k i : ℕ) (ω : Ω) : ℝ :=
  ε ((i : ℤ) + 1) ω * ε ((i : ℤ) + 1 + (k : ℤ)) ω

private lemma sigmaLT_le' (hm : ∀ t, Measurable (ε t)) (t : ℤ) :
    sigmaLT ε t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hm s).comap_le

private lemma comap_le_sigmaLT' {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (ε s) inferInstance ≤ sigmaLT ε t :=
  le_iSup₂_of_le s hst le_rfl

private lemma sigmaLT_mono' {s t : ℤ} (hst : s ≤ t) : sigmaLT ε s ≤ sigmaLT ε t :=
  iSup₂_le fun _ hr => comap_le_sigmaLT' (lt_of_lt_of_le hr hst)

private lemma measurable_sigmaLT' {s t : ℤ} (hst : s < t) : Measurable[sigmaLT ε t] (ε s) :=
  Measurable.of_comap_le (comap_le_sigmaLT' hst)

private lemma measurable_acfProd (hiid : IsIIDNoise ε σ2 μ) (k i : ℕ) :
    Measurable (acfProd ε k i) :=
  (hiid.measurable _).mul (hiid.measurable _)

private lemma abs_acfProd_le (k i : ℕ) (ω : Ω) :
    |acfProd ε k i ω| ≤ (ε ((i : ℤ) + 1) ω ^ 2 + ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2) / 2 := by
  have h := abs_mul (ε ((i : ℤ) + 1) ω) (ε ((i : ℤ) + 1 + (k : ℤ)) ω)
  have h2 := sq_nonneg (|ε ((i : ℤ) + 1) ω| - |ε ((i : ℤ) + 1 + (k : ℤ)) ω|)
  have e1 : |ε ((i : ℤ) + 1) ω| ^ 2 = ε ((i : ℤ) + 1) ω ^ 2 := sq_abs _
  have e2 : |ε ((i : ℤ) + 1 + (k : ℤ)) ω| ^ 2 = ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2 := sq_abs _
  simp only [acfProd, h]
  nlinarith [abs_nonneg (ε ((i : ℤ) + 1) ω), abs_nonneg (ε ((i : ℤ) + 1 + (k : ℤ)) ω)]

private lemma integrable_noise_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) :
    Integrable (fun ω => ε t ω ^ 2) μ :=
  (memLp_two_iff_integrable_sq (hiid.measurable t).aestronglyMeasurable).1 (memLp_noise hiid t)

private lemma indep_noise_sq (hiid : IsIIDNoise ε σ2 μ) {s t : ℤ} (hst : s ≠ t) :
    IndepFun (fun ω => ε s ω ^ 2) (fun ω => ε t ω ^ 2) μ :=
  (hiid.iIndep.indepFun hst).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)

private lemma memLp_acfProd [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) {k : ℕ}
    (hk : 1 ≤ k) (i : ℕ) : MemLp (acfProd ε k i) 2 μ := by
  have hne : ((i : ℤ) + 1) ≠ ((i : ℤ) + 1 + (k : ℤ)) := by
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  refine (memLp_two_iff_integrable_sq (measurable_acfProd hiid k i).aestronglyMeasurable).2 ?_
  have hprod := (indep_noise_sq hiid hne).integrable_mul
    (integrable_noise_sq hiid ((i : ℤ) + 1)) (integrable_noise_sq hiid ((i : ℤ) + 1 + (k : ℤ)))
  refine hprod.congr ?_
  filter_upwards with ω
  simp only [acfProd, Pi.mul_apply]
  ring

private lemma integrable_acfProd [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) {k : ℕ}
    (hk : 1 ≤ k) (i : ℕ) : Integrable (acfProd ε k i) μ :=
  (memLp_acfProd hiid hk i).integrable one_le_two

/-- The martingale-difference property `E[ξ_i | 𝓕_i] = 0`. -/
private lemma condExp_acfProd [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) {k : ℕ}
    (hk : 1 ≤ k) (i : ℕ) :
    μ[acfProd ε k i | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))] =ᵐ[μ] 0 := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hlt : ((i : ℤ) + 1) < ((i : ℤ) + 1 + (k : ℤ)) := by omega
  have hle : sigmaLT ε ((i : ℤ) + 1 + (k : ℤ)) ≤ (inferInstance : MeasurableSpace Ω) :=
    sigmaLT_le' hiid.measurable _
  -- `E[ε_{i+1+k} | 𝓕] = 0`
  have hzero : μ[ε ((i : ℤ) + 1 + (k : ℤ)) | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))] =ᵐ[μ] 0 := by
    have h := condExp_indep_eq (hiid.measurable ((i : ℤ) + 1 + (k : ℤ))).comap_le hle
      (Measurable.stronglyMeasurable
        (Measurable.of_comap_le
          (le_refl (MeasurableSpace.comap (ε ((i : ℤ) + 1 + (k : ℤ))) inferInstance))))
      (indep_noise_sigmaLT hiid.measurable hiid.iIndep ((i : ℤ) + 1 + (k : ℤ)))
    filter_upwards [h] with ω hω
    rw [hω, integral_noise hiid]
    rfl
  have hfun : acfProd ε k i = (ε ((i : ℤ) + 1)) * (ε ((i : ℤ) + 1 + (k : ℤ))) := rfl
  rw [hfun]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := sigmaLT ε ((i : ℤ) + 1 + (k : ℤ)))
    (measurable_sigmaLT' hlt).stronglyMeasurable
    (by rw [← hfun]; exact integrable_acfProd hiid hk i)
    ((memLp_noise hiid _).integrable one_le_two)
  filter_upwards [hpull, hzero] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  simp

/-- The conditional variance `E[ξ_i² | 𝓕_i] = σ² ε_{i+1}²`. -/
private lemma condExp_acfProd_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) {k : ℕ}
    (hk : 1 ≤ k) (i : ℕ) :
    μ[fun ω => acfProd ε k i ω ^ 2 | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))]
      =ᵐ[μ] fun ω => σ2 * ε ((i : ℤ) + 1) ω ^ 2 := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hlt : ((i : ℤ) + 1) < ((i : ℤ) + 1 + (k : ℤ)) := by omega
  have hne : ((i : ℤ) + 1) ≠ ((i : ℤ) + 1 + (k : ℤ)) := by omega
  have hle : sigmaLT ε ((i : ℤ) + 1 + (k : ℤ)) ≤ (inferInstance : MeasurableSpace Ω) :=
    sigmaLT_le' hiid.measurable _
  -- `E[ε_{i+1+k}² | 𝓕] = σ²`
  have hzero : μ[fun ω => ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2
      | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))] =ᵐ[μ] fun _ => σ2 := by
    have h := condExp_indep_eq
      (m₁ := MeasurableSpace.comap (ε ((i : ℤ) + 1 + (k : ℤ))) inferInstance)
      (hiid.measurable ((i : ℤ) + 1 + (k : ℤ))).comap_le hle
      (Measurable.stronglyMeasurable
        ((Measurable.of_comap_le
          (le_refl (MeasurableSpace.comap (ε ((i : ℤ) + 1 + (k : ℤ))) inferInstance))).pow_const 2))
      (indep_noise_sigmaLT hiid.measurable hiid.iIndep ((i : ℤ) + 1 + (k : ℤ)))
    filter_upwards [h] with ω hω
    rw [hω, integral_noise_sq hiid]
  have hprodint : Integrable
      (fun ω => ε ((i : ℤ) + 1) ω ^ 2 * ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2) μ :=
    (indep_noise_sq hiid hne).integrable_mul
      (integrable_noise_sq hiid _) (integrable_noise_sq hiid _)
  have hfun : (fun ω => acfProd ε k i ω ^ 2)
      = (fun ω => ε ((i : ℤ) + 1) ω ^ 2) * (fun ω => ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2) := by
    funext ω; simp only [acfProd, Pi.mul_apply]; ring
  rw [hfun]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := sigmaLT ε ((i : ℤ) + 1 + (k : ℤ)))
    ((measurable_sigmaLT' hlt).pow_const 2).stronglyMeasurable
    hprodint
    (integrable_noise_sq hiid _)
  filter_upwards [hpull, hzero] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  ring

end MDS

section Lindeberg

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- The lag-`k` innovation products are identically distributed: the pair
`(ε_{i+1}, ε_{i+1+k})` has the product law `ν ⊗ ν` for every `i`, by independence and
identical marginals. -/
private lemma identDistrib_acfProd [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    IdentDistrib (acfProd ε k i) (acfProd ε k 0) μ μ := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hne : ∀ j : ℕ, ((j : ℤ) + 1) ≠ ((j : ℤ) + 1 + (k : ℤ)) := fun j => by omega
  have hpair : ∀ j : ℕ,
      μ.map (fun ω => (ε ((j : ℤ) + 1) ω, ε ((j : ℤ) + 1 + (k : ℤ)) ω))
        = (μ.map (ε 0)).prod (μ.map (ε 0)) := by
    intro j
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hiid.measurable _).aemeasurable
      (hiid.measurable _).aemeasurable).1 (hiid.iIndep.indepFun (hne j)),
      (hiid.identDistrib ((j : ℤ) + 1) 0).map_eq,
      (hiid.identDistrib ((j : ℤ) + 1 + (k : ℤ)) 0).map_eq]
  have hid : IdentDistrib (fun ω => (ε ((i : ℤ) + 1) ω, ε ((i : ℤ) + 1 + (k : ℤ)) ω))
      (fun ω => (ε (((0 : ℕ) : ℤ) + 1) ω, ε (((0 : ℕ) : ℤ) + 1 + (k : ℤ)) ω)) μ μ :=
    ⟨((hiid.measurable _).prodMk (hiid.measurable _)).aemeasurable,
      ((hiid.measurable _).prodMk (hiid.measurable _)).aemeasurable, by rw [hpair i, hpair 0]⟩
  exact hid.comp measurable_mul

/-- Every truncated second moment of `ξ_i` is the one of `ξ_0`. -/
private lemma setIntegral_acfProd_eq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (i : ℕ) (c : ℝ) :
    ∫ ω in {ω | c ≤ |acfProd ε k i ω|}, acfProd ε k i ω ^ 2 ∂μ
      = ∫ ω in {ω | c ≤ |acfProd ε k 0 ω|}, acfProd ε k 0 ω ^ 2 ∂μ := by
  classical
  have hφ : Measurable (fun x : ℝ => if c ≤ |x| then x ^ 2 else 0) := by
    refine Measurable.ite (measurableSet_le measurable_const measurable_id.abs) ?_ ?_ <;> fun_prop
  have hrw : ∀ j : ℕ, ∫ ω in {ω | c ≤ |acfProd ε k j ω|}, acfProd ε k j ω ^ 2 ∂μ
      = ∫ ω, (if c ≤ |acfProd ε k j ω| then acfProd ε k j ω ^ 2 else 0) ∂μ := by
    intro j
    rw [← integral_indicator (measurableSet_le measurable_const
      (measurable_acfProd hiid k j).abs)]
    congr 1
  rw [hrw i, hrw 0]
  exact ((identDistrib_acfProd hiid hk i).comp hφ).integral_eq

/-- **The averaged Lindeberg condition** for the lag-`k` innovation products: the terms
are identically distributed, so the average collapses to the single truncated second
moment `E[ξ_0² 1{|ξ_0| ≥ η√n}]`, which vanishes by dominated convergence off `E ξ_0² < ∞`
— no fourth moment of `ε`. -/
private lemma lindeberg_acfProd [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) {k : ℕ}
    (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω in {ω | η * Real.sqrt n ≤ |acfProd ε k i ω|}, acfProd ε k i ω ^ 2 ∂μ)
      atTop (𝓝 0) := by
  classical
  have hsq : Integrable (fun ω => acfProd ε k 0 ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq (measurable_acfProd hiid k 0).aestronglyMeasurable).1
      (memLp_acfProd hiid hk 0)
  -- the single truncated second moment, as an integral of a truncation of `ξ_0²`
  have hF : Tendsto (fun n : ℕ =>
      ∫ ω, (if η * Real.sqrt n ≤ |acfProd ε k 0 ω| then acfProd ε k 0 ω ^ 2 else 0) ∂μ)
      atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => if η * Real.sqrt n ≤ |acfProd ε k 0 ω| then acfProd ε k 0 ω ^ 2 else 0) μ := by
      intro n
      refine (StronglyMeasurable.ite ?_ ?_ ?_).aestronglyMeasurable
      · exact measurableSet_le measurable_const (measurable_acfProd hiid k 0).abs
      · exact ((measurable_acfProd hiid k 0).pow_const 2).stronglyMeasurable
      · exact stronglyMeasurable_const
    have hbnd : ∀ n : ℕ, ∀ᵐ ω ∂μ,
        ‖(if η * Real.sqrt n ≤ |acfProd ε k 0 ω| then acfProd ε k 0 ω ^ 2 else 0)‖
          ≤ acfProd ε k 0 ω ^ 2 := by
      intro n
      filter_upwards with ω
      by_cases hc : η * Real.sqrt n ≤ |acfProd ε k 0 ω|
      · rw [if_pos hc, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      · rw [if_neg hc]
        simpa using sq_nonneg (acfProd ε k 0 ω)
    have hlim : ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => (if η * Real.sqrt n ≤ |acfProd ε k 0 ω| then acfProd ε k 0 ω ^ 2 else 0))
        atTop (𝓝 0) := by
      filter_upwards with ω
      have hgo : Tendsto (fun n : ℕ => η * Real.sqrt n) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hη
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      refine Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ℝ))
      filter_upwards [hgo.eventually_gt_atTop (|acfProd ε k 0 ω|)] with n hn
      rw [if_neg (not_le.2 hn)]
    simpa using tendsto_integral_of_dominated_convergence
      (fun ω => acfProd ε k 0 ω ^ 2) hmeas hsq hbnd hlim
  -- the average is that single term
  refine Tendsto.congr' ?_ hF
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hterm : ∀ i ∈ Finset.range n,
      ∫ ω in {ω | η * Real.sqrt n ≤ |acfProd ε k i ω|}, acfProd ε k i ω ^ 2 ∂μ
        = ∫ ω in {ω | η * Real.sqrt n ≤ |acfProd ε k 0 ω|}, acfProd ε k 0 ω ^ 2 ∂μ :=
    fun i _ => setIntegral_acfProd_eq hiid hk i _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hn0, one_mul,
    ← integral_indicator (measurableSet_le measurable_const (measurable_acfProd hiid k 0).abs)]
  congr 1

/-- `T⁻¹ Σ_{i<T} ε_{i+1}² →p σ²` — the i.i.d. second-moment LLN, as the degenerate
(`c = δ₀`) case of `Consistency.linearProcess_avgSq_tendstoInProb`. -/
private lemma avgSq_noise_tendstoInProb [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤ |(T : ℝ)⁻¹ *
        ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2 - σ2|}).toReal) atTop (𝓝 0) := by
  classical
  set c : ℕ → ℝ := fun n => if n = 0 then (1 : ℝ) else 0 with hc
  have hcs : Summable fun n => |c n| := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hc, hn0]
  have hW : IsLinearProcessOf c ε ε μ := by
    intro t
    refine Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ENNReal))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum : ∀ ω : Ω, ∑ j ∈ Finset.range N, c j * ε (t - (j : ℕ)) ω = ε t ω := by
      intro ω
      rw [Finset.sum_eq_single 0]
      · simp [hc]
      · intro j _ hj; simp [hc, hj]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    have hfun : (fun ω => ε t ω - ∑ j ∈ Finset.range N, c j * ε (t - (j : ℕ)) ω)
        = fun _ => (0 : ℝ) := by
      funext ω; rw [hsum ω]; ring
    rw [hfun]
    simp
  have hts : ∑' n : ℕ, c n ^ 2 = 1 := by
    have : (fun n : ℕ => c n ^ 2) = fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
      funext n; by_cases h : n = 0 <;> simp [hc, h]
    rw [this, tsum_ite_eq]
  have := linearProcess_avgSq_tendstoInProb hiid hcs hW hiid.measurable hδ
  rw [hts] at this
  simpa using this

end Lindeberg

section Moments

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- Markov's inequality in `toReal` form. -/
private lemma markov_toReal [IsProbabilityMeasure μ] {f : Ω → ℝ} (hnn : ∀ ω, 0 ≤ f ω)
    (hint : Integrable f μ) {c : ℝ} (hc : 0 < c) :
    (μ {ω | c ≤ f ω}).toReal ≤ (∫ ω, f ω ∂μ) / c := by
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hnn) hint c
  rw [measureReal_def] at h
  rw [le_div_iff₀ hc, mul_comm]
  exact h

/-- The innovations are orthogonal. -/
private lemma integral_noise_mul [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {s t : ℤ} (hst : s ≠ t) : ∫ ω, ε s ω * ε t ω ∂μ = 0 := by
  rw [(hiid.iIndep.indepFun hst).integral_fun_mul_eq_mul_integral
    (hiid.measurable s).aestronglyMeasurable (hiid.measurable t).aestronglyMeasurable]
  have h : ∫ ω, ε s ω ∂μ = 0 := integral_noise hiid s
  simp [h]

/-- The second moment of a finite sum of orthogonal `L²` variables. -/
private lemma integral_sq_sum_orth [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (s : Finset ℕ)
    (hmem : ∀ i, MemLp (f i) 2 μ)
    (horth : ∀ i j, i ≠ j → ∫ ω, f i ω * f j ω ∂μ = 0) :
    ∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, f i ω ^ 2 ∂μ := by
  classical
  have hint : ∀ i j : ℕ, Integrable (fun ω => f i ω * f j ω) μ := fun i j => by
    have := (hmem i).integrable_mul (hmem j)
    exact this.congr (Eventually.of_forall fun ω => rfl)
  have hexp : ∀ ω, (∑ i ∈ s, f i ω) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i ω * f j ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Eventually.of_forall hexp),
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finset_sum _ (fun j _ => hint i j), Finset.sum_eq_single i]
  · simp [sq]
  · intro j _ hji
    exact horth i j (Ne.symm hji)
  · intro h
    exact absurd hi h

/-- `E[(Σ_{i<T} ε_{i+1})²] = T σ²`. -/
private lemma integral_noiseSum_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (T : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 ∂μ = (T : ℝ) * σ2 := by
  rw [integral_sq_sum_orth (f := fun i : ℕ => ε ((i : ℤ) + 1)) (Finset.range T)
    (fun i => memLp_noise hiid _)
    (fun i j hij => integral_noise_mul hiid (by
      have : (i : ℤ) ≠ (j : ℤ) := by exact_mod_cast hij
      omega))]
  simp [integral_noise_sq hiid]

/-- `E[ξ_i²] = σ⁴`. -/
private lemma integral_acfProd_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : ∫ ω, acfProd ε k i ω ^ 2 ∂μ = σ2 * σ2 := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hne : ((i : ℤ) + 1) ≠ ((i : ℤ) + 1 + (k : ℤ)) := by omega
  have hfun : (fun ω => acfProd ε k i ω ^ 2)
      = fun ω => ε ((i : ℤ) + 1) ω ^ 2 * ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2 := by
    funext ω; simp only [acfProd]; ring
  rw [hfun, (indep_noise_sq hiid hne).integral_fun_mul_eq_mul_integral
    ((hiid.measurable _).pow_const 2).aestronglyMeasurable
    ((hiid.measurable _).pow_const 2).aestronglyMeasurable]
  have h1 : ∫ ω, ε ((i : ℤ) + 1) ω ^ 2 ∂μ = σ2 := integral_noise_sq hiid _
  have h2 : ∫ ω, ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2 ∂μ = σ2 := integral_noise_sq hiid _
  simp [h1, h2]

/-- The martingale-difference orthogonality `E[ξ_i ξ_j] = 0` for `i < j`. -/
private lemma integral_acfProd_mul_of_lt [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) {i j : ℕ} (hij : i < j) :
    ∫ ω, acfProd ε k i ω * acfProd ε k j ω ∂μ = 0 := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hij' : (i : ℤ) < (j : ℤ) := by exact_mod_cast hij
  have hle : sigmaLT ε ((j : ℤ) + 1 + (k : ℤ)) ≤ (inferInstance : MeasurableSpace Ω) :=
    sigmaLT_le' hiid.measurable _
  have hsm : StronglyMeasurable[sigmaLT ε ((j : ℤ) + 1 + (k : ℤ))] (acfProd ε k i) := by
    have h1 : ((i : ℤ) + 1) < ((j : ℤ) + 1 + (k : ℤ)) := by omega
    have h2 : ((i : ℤ) + 1 + (k : ℤ)) < ((j : ℤ) + 1 + (k : ℤ)) := by omega
    exact ((measurable_sigmaLT' h1).mul (measurable_sigmaLT' h2)).stronglyMeasurable
  have hprodint : Integrable (acfProd ε k i * acfProd ε k j) μ :=
    (memLp_acfProd hiid hk i).integrable_mul (memLp_acfProd hiid hk j)
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := sigmaLT ε ((j : ℤ) + 1 + (k : ℤ)))
    hsm hprodint (integrable_acfProd hiid hk j)
  have hzero : (acfProd ε k i) * μ[acfProd ε k j | sigmaLT ε ((j : ℤ) + 1 + (k : ℤ))]
      =ᵐ[μ] 0 := by
    filter_upwards [condExp_acfProd hiid hk j] with ω hω
    simp [Pi.mul_apply, hω]
  have hcond : μ[acfProd ε k i * acfProd ε k j | sigmaLT ε ((j : ℤ) + 1 + (k : ℤ))] =ᵐ[μ] 0 :=
    hpull.trans hzero
  have hI := integral_condExp (μ := μ) (m := sigmaLT ε ((j : ℤ) + 1 + (k : ℤ)))
    (f := acfProd ε k i * acfProd ε k j) hle
  rw [integral_congr_ae hcond] at hI
  simp only [Pi.zero_apply, integral_zero] at hI
  have hfun : (fun ω => acfProd ε k i ω * acfProd ε k j ω)
      = (acfProd ε k i * acfProd ε k j) := rfl
  rw [hfun]
  exact hI.symm

/-- `E[(Σ_{i<T} ξ_i)²] = T σ⁴`. -/
private lemma integral_crossSum_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range T, acfProd ε k i ω) ^ 2 ∂μ = (T : ℝ) * (σ2 * σ2) := by
  have horth : ∀ i j : ℕ, i ≠ j → ∫ ω, acfProd ε k i ω * acfProd ε k j ω ∂μ = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact integral_acfProd_mul_of_lt hiid hk h
    · rw [show (fun ω => acfProd ε k i ω * acfProd ε k j ω)
        = fun ω => acfProd ε k j ω * acfProd ε k i ω from funext fun ω => mul_comm _ _]
      exact integral_acfProd_mul_of_lt hiid hk h
  rw [integral_sq_sum_orth (Finset.range T) (fun i => memLp_acfProd hiid hk i) horth]
  simp [integral_acfProd_sq hiid hk]

end Moments

section CLT

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- **The martingale CLT for the raw lag-`k` cross sum**: `T^{-1/2} Σ_{i<T} ε_{i+1}ε_{i+1+k}`
is asymptotically `N(0, σ⁴)`. Only two moments of `ε` are used. -/
private theorem crossSum_clt [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, acfProd ε k i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (σ2 * σ2))) u)) := by
  classical
  refine mds_clt_sequence (G := fun i : ℕ => sigmaLT ε ((i : ℤ) + 1 + (k : ℤ)))
    (fun i => sigmaLT_le' hiid.measurable _)
    (fun i j hij => sigmaLT_mono' (by
      have : (i : ℤ) ≤ (j : ℤ) := Int.ofNat_le.2 hij
      omega))
    (fun i => ?_) (fun i => memLp_acfProd hiid hk i) (fun i => condExp_acfProd hiid hk i)
    (mul_self_nonneg σ2) ?_ (fun η hη => lindeberg_acfProd hiid hk hη) u
  · -- adaptedness
    have h1 : ((i : ℤ) + 1) < (((i + 1 : ℕ) : ℤ) + 1 + (k : ℤ)) := by
      have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      push_cast
      omega
    have h2 : ((i : ℤ) + 1 + (k : ℤ)) < (((i + 1 : ℕ) : ℤ) + 1 + (k : ℤ)) := by
      push_cast
      omega
    exact (measurable_sigmaLT' h1).mul (measurable_sigmaLT' h2)
  · -- the conditional-variance LLN
    intro δ hδ
    have hδ' : 0 < δ / σ2 := by positivity
    have hset : ∀ n : ℕ,
        {ω | δ ≤ |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n,
            μ[fun ω' => acfProd ε k i ω' ^ 2 | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))] ω)
              - σ2 * σ2|}
          =ᵐ[μ] {ω | δ / σ2 ≤ |(n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, ε ((i : ℤ) + 1) ω ^ 2 - σ2|} := by
      intro n
      have hall : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n,
          μ[fun ω' => acfProd ε k i ω' ^ 2 | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))] ω
            = σ2 * ε ((i : ℤ) + 1) ω ^ 2 := by
        rw [ae_all_iff]
        intro i
        rw [eventually_imp_distrib_left]
        exact fun _ => condExp_acfProd_sq hiid hk i
      rw [Filter.eventuallyEq_set]
      filter_upwards [hall] with ω hω
      have hsum : ∑ i ∈ Finset.range n,
          μ[fun ω' => acfProd ε k i ω' ^ 2 | sigmaLT ε ((i : ℤ) + 1 + (k : ℤ))] ω
            = σ2 * ∑ i ∈ Finset.range n, ε ((i : ℤ) + 1) ω ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hω
      simp only [Set.mem_setOf_eq, hsum]
      have hfac : (n : ℝ)⁻¹ * (σ2 * ∑ i ∈ Finset.range n, ε ((i : ℤ) + 1) ω ^ 2) - σ2 * σ2
          = σ2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ε ((i : ℤ) + 1) ω ^ 2 - σ2) := by
        ring
      rw [hfac, abs_mul, abs_of_pos hσ]
      constructor
      · intro h
        rw [div_le_iff₀ hσ, mul_comm]
        exact h
      · intro h
        rw [div_le_iff₀ hσ, mul_comm] at h
        exact h
    have hbase := avgSq_noise_tendstoInProb hiid hδ'
    refine hbase.congr fun n => ?_
    rw [measure_congr (hset n)]

end CLT

section Algebra

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

private lemma acfProd_eq_shift (k i : ℕ) (ω : Ω) :
    acfProd ε k i ω = ε ((i : ℤ) + 1) ω * ε (((i + k : ℕ) : ℤ) + 1) ω := by
  simp only [acfProd]
  congr 2
  push_cast
  ring

private lemma sampleMean_eq_range (T : ℕ) (ω : Ω) :
    sampleMean (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω)
      = (T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω := by
  simp only [sampleMean]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => ε ((i : ℤ) + 1) ω) T

/-- The exact mean-correction decomposition of the lag-`k` sample autocovariance. -/
private lemma sampleACVF_decomp (k T : ℕ) (hkT : k ≤ T) (ω : Ω) :
    sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
      = (T : ℝ)⁻¹ * ((∑ i ∈ Finset.range (T - k), acfProd ε k i ω)
          - sampleMean (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) *
              ((∑ i ∈ Finset.range (T - k), ε ((i : ℤ) + 1) ω)
                + ∑ i ∈ Finset.Ico k T, ε ((i : ℤ) + 1) ω)
          + ((T - k : ℕ) : ℝ) *
              sampleMean (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) ^ 2) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = sampleMean (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) := ⟨_, rfl⟩
  simp only [sampleACVF, ← hc]
  congr 1
  -- pass to a sum over `range T`
  have hpt : ∀ t : Fin T,
      (if h : (t : ℕ) + k < T then
        ((fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) t - c) *
          ((fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) ⟨(t : ℕ) + k, h⟩ - c) else 0)
      = (if (t : ℕ) + k < T then
          (ε (((t : ℕ) : ℤ) + 1) ω - c) * (ε ((((t : ℕ) + k : ℕ) : ℤ) + 1) ω - c) else 0) := by
    intro t
    by_cases h : (t : ℕ) + k < T
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun t _ => hpt t,
    Fin.sum_univ_eq_sum_range (fun i => if i + k < T then
      (ε ((i : ℤ) + 1) ω - c) * (ε (((i + k : ℕ) : ℤ) + 1) ω - c) else 0) T]
  -- the window collapses to `range (T − k)`
  have hwin : ∑ i ∈ Finset.range T, (if i + k < T then
        (ε ((i : ℤ) + 1) ω - c) * (ε (((i + k : ℕ) : ℤ) + 1) ω - c) else 0)
      = ∑ i ∈ Finset.range (T - k),
          (ε ((i : ℤ) + 1) ω - c) * (ε (((i + k : ℕ) : ℤ) + 1) ω - c) := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hwin]
  -- expand the product
  have hexp : ∑ i ∈ Finset.range (T - k),
        (ε ((i : ℤ) + 1) ω - c) * (ε (((i + k : ℕ) : ℤ) + 1) ω - c)
      = ∑ i ∈ Finset.range (T - k),
          (acfProd ε k i ω - c * ε ((i : ℤ) + 1) ω - c * ε (((i + k : ℕ) : ℤ) + 1) ω + c ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [acfProd_eq_shift]
    ring
  rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- reindex the shifted sum
  have hshift : ∑ i ∈ Finset.range (T - k), ε (((i + k : ℕ) : ℤ) + 1) ω
      = ∑ i ∈ Finset.Ico k T, ε ((i : ℤ) + 1) ω := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr (by rw [show T - k = T - k from rfl]) fun i _ => by
      congr 2
      push_cast
      ring
  rw [hshift]
  ring

end Algebra

section ErrorBound

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- The pure real-arithmetic core of the error bound. -/
private lemma arith_key {C E S D1 D2 q Tr kr A : ℝ}
    (hq0 : 0 < q) (hqT : q * Tr = 1) (hk0 : 0 ≤ kr) (hkTr : kr ≤ Tr) (hEabs : |E| ≤ A) :
    |C - E - q * S * (S - D1 + (S - D2)) + (Tr - kr) * (q * S) ^ 2 - C|
      ≤ A + q * (4 * S ^ 2 + D1 ^ 2 + D2 ^ 2) := by
  have hfac : 0 ≤ (Tr - kr) * q := mul_nonneg (by linarith) hq0.le
  have hfac1 : (Tr - kr) * q ≤ 1 := by
    have h1 : (Tr - kr) * q = q * Tr - kr * q := by ring
    have h2 : 0 ≤ kr * q := mul_nonneg hk0 hq0.le
    rw [h1, hqT]
    linarith
  have e1 : C - E - q * S * (S - D1 + (S - D2)) + (Tr - kr) * (q * S) ^ 2 - C
      = -E - q * (S * (2 * S - D1 - D2)) + ((Tr - kr) * q) * (q * S ^ 2) := by ring
  rw [e1]
  have t1 : |-E - q * (S * (2 * S - D1 - D2)) + ((Tr - kr) * q) * (q * S ^ 2)|
      ≤ |-E - q * (S * (2 * S - D1 - D2))| + |((Tr - kr) * q) * (q * S ^ 2)| := abs_add_le _ _
  have t2 : |-E - q * (S * (2 * S - D1 - D2))| ≤ |E| + |q * (S * (2 * S - D1 - D2))| := by
    have h := abs_sub (-E) (q * (S * (2 * S - D1 - D2)))
    rw [abs_neg] at h
    exact h
  have t3 : |q * (S * (2 * S - D1 - D2))| ≤ q * (3 * S ^ 2 + (D1 ^ 2 + D2 ^ 2) / 2) := by
    rw [abs_mul, abs_of_pos hq0]
    refine mul_le_mul_of_nonneg_left ?_ hq0.le
    have h5 : |S * (2 * S - D1 - D2)| = |S| * |2 * S - D1 - D2| := abs_mul _ _
    have h6 : |2 * S - D1 - D2| ≤ 2 * |S| + |D1| + |D2| := by
      have a1 : |2 * S - D1 - D2| ≤ |2 * S - D1| + |D2| := abs_sub _ _
      have a2 : |2 * S - D1| ≤ |2 * S| + |D1| := abs_sub _ _
      have a3 : |2 * S| = 2 * |S| := by rw [abs_mul]; simp
      linarith
    have h7 : |S| * |2 * S - D1 - D2| ≤ |S| * (2 * |S| + |D1| + |D2|) :=
      mul_le_mul_of_nonneg_left h6 (abs_nonneg S)
    have h8 : |S| * |S| = S ^ 2 := by rw [← sq_abs S]; ring
    have h9 : |S| * |D1| ≤ (S ^ 2 + D1 ^ 2) / 2 := by
      nlinarith [sq_nonneg (|S| - |D1|), sq_abs S, sq_abs D1]
    have h10 : |S| * |D2| ≤ (S ^ 2 + D2 ^ 2) / 2 := by
      nlinarith [sq_nonneg (|S| - |D2|), sq_abs S, sq_abs D2]
    have hexpand : |S| * (2 * |S| + |D1| + |D2|) = 2 * (|S| * |S|) + |S| * |D1| + |S| * |D2| := by
      ring
    rw [h5]
    linarith [h7, hexpand.le, hexpand.ge, h8, h9, h10]
  have t4 : |((Tr - kr) * q) * (q * S ^ 2)| ≤ q * S ^ 2 := by
    have hqS : (0 : ℝ) ≤ q * S ^ 2 := by positivity
    rw [abs_of_nonneg (mul_nonneg hfac hqS)]
    have := mul_le_mul_of_nonneg_right hfac1 hqS
    linarith [this]
  have t5 : q * (3 * S ^ 2 + (D1 ^ 2 + D2 ^ 2) / 2) + q * S ^ 2
      ≤ q * (4 * S ^ 2 + D1 ^ 2 + D2 ^ 2) := by
    have hid : q * (4 * S ^ 2 + D1 ^ 2 + D2 ^ 2)
        - (q * (3 * S ^ 2 + (D1 ^ 2 + D2 ^ 2) / 2) + q * S ^ 2) = q * ((D1 ^ 2 + D2 ^ 2) / 2) := by
      ring
    have hnn : (0 : ℝ) ≤ q * ((D1 ^ 2 + D2 ^ 2) / 2) := by positivity
    linarith [hid, hnn]
  linarith

/-- The `L¹` envelope of the mean-correction/edge error of the lag-`k` sample
autocovariance. -/
private noncomputable def errBound (ε : ℤ → Ω → ℝ) (k T : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω|)
    + (T : ℝ)⁻¹ * (4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2)

private lemma errBound_nonneg (k T : ℕ) (ω : Ω) : 0 ≤ errBound ε k T ω := by
  unfold errBound
  have h1 : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ (T : ℝ)⁻¹ * (4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2) := by positivity
  linarith

/-- **The pointwise error bound**: the difference between the scaled sample autocovariance
and the scaled raw cross sum is dominated by `T^{-1/2}·errBound`. -/
private lemma abs_sqrt_sampleACVF_sub_le (k T : ℕ) (hkT : k ≤ T) (hT : 0 < T) (ω : Ω) :
    |Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
        - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω|
      ≤ (Real.sqrt T)⁻¹ * errBound ε k T ω := by
  classical
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hrpos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
  have hrr : Real.sqrt (T : ℝ) * Real.sqrt (T : ℝ) = (T : ℝ) := Real.mul_self_sqrt hTpos.le
  have hstep : Real.sqrt (T : ℝ) * (T : ℝ)⁻¹ = (Real.sqrt (T : ℝ))⁻¹ := by
    field_simp
    linarith [hrr]
  rw [sampleACVF_decomp k T hkT ω, sampleMean_eq_range, ← mul_assoc, hstep, ← mul_sub,
    abs_mul, abs_of_pos (inv_pos.2 hrpos)]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.2 hrpos))
  -- decompose the three window sums
  have hC' : ∑ i ∈ Finset.range (T - k), acfProd ε k i ω
      = (∑ i ∈ Finset.range T, acfProd ε k i ω)
        - ∑ i ∈ Finset.Ico (T - k) T, acfProd ε k i ω := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive (fun i => acfProd ε k i ω) (Nat.zero_le (T - k))
        (Nat.sub_le T k)]
    ring
  have hU : ∑ i ∈ Finset.range (T - k), ε ((i : ℤ) + 1) ω
      = (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω)
        - ∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive (fun i => ε ((i : ℤ) + 1) ω) (Nat.zero_le (T - k))
        (Nat.sub_le T k)]
    ring
  have hV : ∑ i ∈ Finset.Ico k T, ε ((i : ℤ) + 1) ω
      = (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω)
        - ∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive (fun i => ε ((i : ℤ) + 1) ω) (Nat.zero_le k) hkT]
    ring
  have hcast : ((T - k : ℕ) : ℝ) = (T : ℝ) - (k : ℝ) := Nat.cast_sub hkT
  rw [hC', hU, hV, hcast]
  -- abstract the five quantities
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = ∑ i ∈ Finset.range T, acfProd ε k i ω := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = ∑ i ∈ Finset.Ico (T - k) T, acfProd ε k i ω := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω := ⟨_, rfl⟩
  obtain ⟨D1, hD1d⟩ : ∃ D : ℝ, D = ∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω := ⟨_, rfl⟩
  obtain ⟨D2, hD2d⟩ : ∃ D : ℝ, D = ∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω := ⟨_, rfl⟩
  have hEabs : |E| ≤ ∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω| := by
    rw [hEd]; exact Finset.abs_sum_le_sum_abs _ _
  have hAnn : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [← hCd, ← hEd, ← hSd, ← hD1d, ← hD2d]
  unfold errBound
  rw [← hSd, ← hD1d, ← hD2d]
  -- pure real arithmetic
  obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = (T : ℝ)⁻¹ := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqd]; positivity
  have hqT : q * (T : ℝ) = 1 := by rw [hqd]; field_simp
  have hkT' : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hkT
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [← hqd]
  exact arith_key hq0 hqT hk0 hkT' hEabs

end ErrorBound

section Transfers

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

private lemma memLp_noiseFinsetSum (hiid : IsIIDNoise ε σ2 μ) (s : Finset ℕ) :
    MemLp (fun ω => ∑ i ∈ s, ε ((i : ℤ) + 1) ω) 2 μ :=
  memLp_finset_sum s fun i _ => memLp_noise hiid _

/-- `E[(Σ_{i ∈ s} ε_{i+1})²] = #s · σ²`. -/
private lemma integral_noiseFinsetSum_sq [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (s : Finset ℕ) :
    ∫ ω, (∑ i ∈ s, ε ((i : ℤ) + 1) ω) ^ 2 ∂μ = (s.card : ℝ) * σ2 := by
  rw [integral_sq_sum_orth (f := fun i : ℕ => ε ((i : ℤ) + 1)) s
    (fun i => memLp_noise hiid _)
    (fun i j hij => integral_noise_mul hiid (by
      have : (i : ℤ) ≠ (j : ℤ) := by exact_mod_cast hij
      omega))]
  simp [integral_noise_sq hiid]

private lemma integral_abs_acfProd_le [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : ∫ ω, |acfProd ε k i ω| ∂μ ≤ σ2 := by
  have hint2 : Integrable
      (fun ω => (ε ((i : ℤ) + 1) ω ^ 2 + ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2) / 2) μ :=
    ((integrable_noise_sq hiid _).add (integrable_noise_sq hiid _)).div_const 2
  have hmono := integral_mono (integrable_acfProd hiid hk i).abs hint2
    (fun ω => abs_acfProd_le k i ω)
  have hval : ∫ ω, (ε ((i : ℤ) + 1) ω ^ 2 + ε ((i : ℤ) + 1 + (k : ℤ)) ω ^ 2) / 2 ∂μ = σ2 := by
    rw [integral_div, integral_add (integrable_noise_sq hiid _) (integrable_noise_sq hiid _),
      integral_noise_sq hiid, integral_noise_sq hiid]
    ring
  rw [hval] at hmono
  exact hmono

private lemma integrable_errBound [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (T : ℕ) : Integrable (errBound ε k T) μ := by
  unfold errBound
  refine Integrable.add (integrable_finset_sum _ fun i _ => (integrable_acfProd hiid hk i).abs) ?_
  refine Integrable.const_mul ?_ _
  have hsq : ∀ s : Finset ℕ, Integrable (fun ω => (∑ i ∈ s, ε ((i : ℤ) + 1) ω) ^ 2) μ :=
    fun s => (memLp_two_iff_integrable_sq
      (memLp_noiseFinsetSum hiid s).aestronglyMeasurable).1 (memLp_noiseFinsetSum hiid s)
  exact (((hsq _).const_mul 4).add (hsq _)).add (hsq _)

private lemma integral_errBound_le [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (hσ : 0 < σ2) {k T : ℕ} (hk : 1 ≤ k) (hkT : k ≤ T) (hT : 1 ≤ T) :
    ∫ ω, errBound ε k T ω ∂μ ≤ σ2 * (3 * (k : ℝ) + 4) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hsq : ∀ s : Finset ℕ, Integrable (fun ω => (∑ i ∈ s, ε ((i : ℤ) + 1) ω) ^ 2) μ :=
    fun s => (memLp_two_iff_integrable_sq
      (memLp_noiseFinsetSum hiid s).aestronglyMeasurable).1 (memLp_noiseFinsetSum hiid s)
  have hA : Integrable (fun ω => 4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2) μ :=
    (hsq _).const_mul 4
  have hB : Integrable
      (fun ω => (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2) μ := hsq _
  have hC : Integrable (fun ω => (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2) μ := hsq _
  have hAB : Integrable (fun ω => 4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
      + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2) μ := hA.add hB
  have hI1 : Integrable (fun ω => ∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω|) μ :=
    integrable_finset_sum _ fun i _ => (integrable_acfProd hiid hk i).abs
  have hI2 : Integrable (fun ω => (T : ℝ)⁻¹ *
      (4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2)) μ :=
    (hAB.add hC).const_mul _
  have hsplit : ∫ ω, errBound ε k T ω ∂μ
      = (∫ ω, ∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω| ∂μ)
        + ∫ ω, (T : ℝ)⁻¹ * (4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
            + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2
            + (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2) ∂μ := by
    unfold errBound
    exact integral_add hI1 hI2
  rw [hsplit]
  -- the edge sum of `|ξ_i|`
  have h1 : ∫ ω, ∑ i ∈ Finset.Ico (T - k) T, |acfProd ε k i ω| ∂μ ≤ (k : ℝ) * σ2 := by
    rw [integral_finset_sum _ fun i _ => (integrable_acfProd hiid hk i).abs]
    have hle : ∑ i ∈ Finset.Ico (T - k) T, ∫ ω, |acfProd ε k i ω| ∂μ
        ≤ ∑ _i ∈ Finset.Ico (T - k) T, σ2 :=
      Finset.sum_le_sum fun i _ => integral_abs_acfProd_le hiid hk i
    have hcard : (Finset.Ico (T - k) T).card = k := by
      rw [Nat.card_Ico]
      omega
    rwa [Finset.sum_const, hcard, nsmul_eq_mul] at hle
  -- the quadratic part
  have hbig : ∫ ω, (4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2) ∂μ
      = 4 * ((T : ℝ) * σ2) + (k : ℝ) * σ2 + (k : ℝ) * σ2 := by
    have e1 := integral_add hAB hC
    have e2 := integral_add hA hB
    have e3 : ∫ ω, 4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 ∂μ
        = 4 * ∫ ω, (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 ∂μ := integral_const_mul _ _
    have hc1 : ((Finset.range T).card : ℝ) = (T : ℝ) := by simp
    have hc2 : ((Finset.Ico (T - k) T).card : ℝ) = (k : ℝ) := by
      rw [Nat.card_Ico]
      have hcc : T - (T - k) = k := by omega
      rw [hcc]
    have hc3 : ((Finset.range k).card : ℝ) = (k : ℝ) := by simp
    rw [e1, e2, e3, integral_noiseFinsetSum_sq hiid, integral_noiseFinsetSum_sq hiid,
      integral_noiseFinsetSum_sq hiid, hc1, hc2, hc3]
  have h2 : ∫ ω, (T : ℝ)⁻¹ * (4 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.Ico (T - k) T, ε ((i : ℤ) + 1) ω) ^ 2
        + (∑ i ∈ Finset.range k, ε ((i : ℤ) + 1) ω) ^ 2) ∂μ
      ≤ 4 * σ2 + 2 * (k : ℝ) * σ2 := by
    rw [integral_const_mul, hbig]
    have hkey : (T : ℝ)⁻¹ * (4 * ((T : ℝ) * σ2) + (k : ℝ) * σ2 + (k : ℝ) * σ2)
        = 4 * σ2 + (T : ℝ)⁻¹ * (2 * (k : ℝ) * σ2) := by
      field_simp
      ring
    rw [hkey]
    have hle1 : (T : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact_mod_cast hT
    have hnn : (0 : ℝ) ≤ 2 * (k : ℝ) * σ2 := by positivity
    nlinarith
  have hcomb : (k : ℝ) * σ2 + (4 * σ2 + 2 * (k : ℝ) * σ2) = σ2 * (3 * (k : ℝ) + 4) := by ring
  linarith

/-- **The `√T`-scaled sample autocovariance is the raw cross sum up to `o_p(1)`.** -/
private lemma tendstoInProb_sampleACVF_sub [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (hσ : 0 < σ2) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
          - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω|}).toReal)
      atTop (𝓝 0) := by
  have hbig : ∀ T : ℕ, max k 1 ≤ T →
      (μ {ω | δ ≤
        |Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
          - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω|}).toReal
        ≤ σ2 * (3 * (k : ℝ) + 4) / (δ * Real.sqrt T) := by
    intro T hT
    have hkT : k ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
    have hrpos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
    have hsub : {ω | δ ≤
        |Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
          - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω|}
        ⊆ {ω | δ * Real.sqrt T ≤ errBound ε k T ω} := by
      intro ω hω
      have hpt := abs_sqrt_sampleACVF_sub_le (ε := ε) k T hkT (by omega) ω
      have h1 : δ ≤ (Real.sqrt T)⁻¹ * errBound ε k T ω := le_trans hω hpt
      have h2 := mul_le_mul_of_nonneg_right h1 hrpos.le
      rw [inv_mul_eq_div, div_mul_cancel₀ _ (ne_of_gt hrpos)] at h2
      exact h2
    have hmono := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    have hmk := markov_toReal (f := errBound ε k T) (errBound_nonneg k T)
      (integrable_errBound hiid hk T) (c := δ * Real.sqrt T) (by positivity)
    have hIle := integral_errBound_le hiid hσ hk hkT hT1
    have hdiv : (∫ ω, errBound ε k T ω ∂μ) / (δ * Real.sqrt T)
        ≤ σ2 * (3 * (k : ℝ) + 4) / (δ * Real.sqrt T) := by
      apply div_le_div_of_nonneg_right hIle (by positivity)
    linarith
  have hlim : Tendsto (fun T : ℕ => σ2 * (3 * (k : ℝ) + 4) / (δ * Real.sqrt T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => δ * Real.sqrt (T : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hδ
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with T
    exact ENNReal.toReal_nonneg
  · filter_upwards [eventually_ge_atTop (max k 1)] with T hT
    exact hbig T hT

end Transfers

section Ratio

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

private lemma toReal_measure_le_union₃ [IsFiniteMeasure μ] {A B C E : Set Ω}
    (h : A ⊆ B ∪ C ∪ E) :
    (μ A).toReal ≤ (μ B).toReal + (μ C).toReal + (μ E).toReal := by
  have h4 : μ A ≤ μ B + μ C + μ E := by
    refine le_trans (measure_mono h) (le_trans (measure_union_le _ _) ?_)
    gcongr
    exact measure_union_le _ _
  have hfin : μ B + μ C + μ E ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩,
      measure_ne_top _ _⟩
  calc (μ A).toReal ≤ (μ B + μ C + μ E).toReal := ENNReal.toReal_mono hfin h4
    _ = (μ B).toReal + (μ C).toReal + (μ E).toReal := by
        rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          (measure_ne_top _ _), ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

/-- **The quotient Slutsky step**: if `A_T` is bounded in `L²`, `Δ_T →p 0` and
`D_T →p σ² > 0`, then `(A_T + Δ_T)/D_T − A_T/σ² →p 0`. -/
private lemma tendstoInProb_ratio [IsProbabilityMeasure μ] {A Δ D : ℕ → Ω → ℝ} {K : ℝ}
    (hσ : 0 < σ2) (hK : 0 < K)
    (hAint : ∀ T, Integrable (fun ω => A T ω ^ 2) μ)
    (hAsq : ∀ T, ∫ ω, A T ω ^ 2 ∂μ ≤ K)
    (hΔ : ∀ δ : ℝ, 0 < δ → Tendsto (fun T => (μ {ω | δ ≤ |Δ T ω|}).toReal) atTop (𝓝 0))
    (hD : ∀ δ : ℝ, 0 < δ → Tendsto (fun T => (μ {ω | δ ≤ |D T ω - σ2|}).toReal) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T => (μ {ω | δ ≤ |(A T ω + Δ T ω) / D T ω - A T ω / σ2|}).toReal)
      atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ζ hζ => ?_
  -- the truncation level for `A`
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 < lam ∧ K / lam ^ 2 < ζ / 3 := by
    refine ⟨Real.sqrt (3 * K / ζ) + 1, by positivity, ?_⟩
    have h0 : 0 ≤ Real.sqrt (3 * K / ζ) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (3 * K / ζ) ^ 2 = 3 * K / ζ :=
      Real.sq_sqrt (by positivity)
    have hgt : 3 * K / ζ < (Real.sqrt (3 * K / ζ) + 1) ^ 2 := by nlinarith
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have h3 : 0 < 3 * K / ζ := by positivity
    have h4 : ζ * (3 * K / ζ) = 3 * K := by field_simp
    have h5 : ζ * (3 * K / ζ) < ζ * (Real.sqrt (3 * K / ζ) + 1) ^ 2 :=
      mul_lt_mul_of_pos_left hgt hζ
    linarith
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ σ2 / 2 ∧ lam * η ≤ δ * σ2 ^ 2 / 8 :=
    ⟨min (σ2 / 2) (δ * σ2 ^ 2 / (8 * lam)), by positivity, min_le_left _ _, by
      have h1 : min (σ2 / 2) (δ * σ2 ^ 2 / (8 * lam)) ≤ δ * σ2 ^ 2 / (8 * lam) :=
        min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_left h1 hlam0.le
      have h3 : lam * (δ * σ2 ^ 2 / (8 * lam)) = δ * σ2 ^ 2 / 8 := by
        field_simp
      linarith [h3.le, h3.ge]⟩
  obtain ⟨δ', hδ'0, hδ'⟩ : ∃ δ' : ℝ, 0 < δ' ∧ σ2 * δ' = δ * σ2 ^ 2 / 8 :=
    ⟨δ * σ2 / 8, by positivity, by ring⟩
  -- the Chebyshev bound on the truncation event
  have hA : ∀ T : ℕ, (μ {ω | lam ≤ |A T ω|}).toReal ≤ K / lam ^ 2 := by
    intro T
    have hsub : {ω | lam ≤ |A T ω|} ⊆ {ω | lam ^ 2 ≤ A T ω ^ 2} := by
      intro ω hω
      have h1 : lam ≤ |A T ω| := hω
      have h2 : lam ^ 2 ≤ |A T ω| ^ 2 := by nlinarith [abs_nonneg (A T ω)]
      simpa [sq_abs] using h2
    have hmono := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    have hmk := markov_toReal (f := fun ω => A T ω ^ 2) (fun ω => sq_nonneg _) (hAint T)
      (c := lam ^ 2) (by positivity)
    have hdiv : (∫ ω, A T ω ^ 2 ∂μ) / lam ^ 2 ≤ K / lam ^ 2 :=
      div_le_div_of_nonneg_right (hAsq T) (by positivity)
    linarith
  have hev1 := (hD η hη0).eventually_lt_const (show (0:ℝ) < ζ / 3 by linarith)
  have hev2 := (hΔ δ' hδ'0).eventually_lt_const (show (0:ℝ) < ζ / 3 by linarith)
  filter_upwards [hev1, hev2] with T hT1 hT2
  have hsub : {ω | δ ≤ |(A T ω + Δ T ω) / D T ω - A T ω / σ2|}
      ⊆ {ω | lam ≤ |A T ω|} ∪ {ω | η ≤ |D T ω - σ2|} ∪ {ω | δ' ≤ |Δ T ω|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨⟨hA', hD'⟩, hΔ'⟩ := hcon
    have hDpos : 0 < D T ω := by
      have : |D T ω - σ2| < σ2 / 2 := lt_of_lt_of_le hD' hη1
      have h2 : -(σ2 / 2) < D T ω - σ2 := neg_lt_of_abs_lt this
      linarith
    have hDhalf : σ2 / 2 ≤ D T ω := by
      have : |D T ω - σ2| < σ2 / 2 := lt_of_lt_of_le hD' hη1
      have h2 : -(σ2 / 2) < D T ω - σ2 := neg_lt_of_abs_lt this
      linarith
    have hid : (A T ω + Δ T ω) / D T ω - A T ω / σ2
        = (A T ω * (σ2 - D T ω) + σ2 * Δ T ω) / (D T ω * σ2) := by
      field_simp
      ring
    have hnum : |A T ω * (σ2 - D T ω) + σ2 * Δ T ω| ≤ lam * η + σ2 * δ' := by
      have h1 : |A T ω * (σ2 - D T ω)| ≤ lam * η := by
        rw [abs_mul]
        have hle1 : |A T ω| ≤ lam := le_of_lt hA'
        have hle2 : |σ2 - D T ω| ≤ η := by
          rw [abs_sub_comm]
          exact le_of_lt hD'
        exact mul_le_mul hle1 hle2 (abs_nonneg _) hlam0.le
      have h2 : |σ2 * Δ T ω| ≤ σ2 * δ' := by
        rw [abs_mul, abs_of_pos hσ]
        exact mul_le_mul_of_nonneg_left (le_of_lt hΔ') hσ.le
      have h3 := abs_add_le (A T ω * (σ2 - D T ω)) (σ2 * Δ T ω)
      linarith
    have hbound : |(A T ω + Δ T ω) / D T ω - A T ω / σ2| ≤ δ / 2 := by
      rw [hid, abs_div, abs_of_pos (by positivity : 0 < D T ω * σ2), div_le_iff₀ (by positivity)]
      have hrhs : δ * σ2 ^ 2 / 4 ≤ δ / 2 * (D T ω * σ2) := by
        have h1 : σ2 / 2 * σ2 ≤ D T ω * σ2 := mul_le_mul_of_nonneg_right hDhalf hσ.le
        nlinarith
      have hsum : lam * η + σ2 * δ' ≤ δ * σ2 ^ 2 / 4 := by
        rw [hδ']
        linarith
      linarith
    have : δ ≤ δ / 2 := le_trans hω hbound
    linarith
  have hfinal := toReal_measure_le_union₃ (μ := μ) hsub
  have hnn : (0:ℝ) ≤ (μ {ω | δ ≤ |(A T ω + Δ T ω) / D T ω - A T ω / σ2|}).toReal :=
    ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have := hA T
  linarith [hT1, hT2]

end Ratio

section Assembly

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

-- STUB (exists in `ARMA/Diagnostics.lean`)
private lemma measurable_sampleACF₂ {T : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, Measurable (Z t))
    (m : ℕ) :
    Measurable fun ω => sampleACF (fun t : Fin T => Z (((t : ℕ) : ℤ) + 1) ω) m := by
  sorry

-- STUB (exists in `ARMA/Diagnostics.lean`)
private lemma tendsto_charFun_of_tendstoInProb_sub₂ [IsProbabilityMeasure μ]
    {Y Z : ℕ → Ω → ℝ} (hY : ∀ T, Measurable (Y T)) (hZ : ∀ T, Measurable (Z T))
    {L : ℂ} {u : ℝ}
    (hlim : Tendsto (fun T => charFun (μ.map (Y T)) u) atTop (𝓝 L))
    (hsub : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun T => (μ {ω | δ ≤ |Z T ω - Y T ω|}).toReal) atTop (𝓝 0)) :
    Tendsto (fun T => charFun (μ.map (Z T)) u) atTop (𝓝 L) := by
  sorry

/-- `γ̂(0) = T⁻¹ Σ ε² − (T⁻¹ Σ ε)²`. -/
private lemma sampleACVF_zero_eq (T : ℕ) (hT : 0 < T) (ω : Ω) :
    sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) 0
      = (T : ℝ)⁻¹ * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2)
        - ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 := by
  have hTne : ((T : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    exact ne_of_gt this
  rw [sampleACVF_decomp 0 T (Nat.zero_le T) ω, sampleMean_eq_range]
  simp only [Nat.sub_zero]
  have hprod : ∀ i ∈ Finset.range T, acfProd ε 0 i ω = ε ((i : ℤ) + 1) ω ^ 2 := by
    intro i _
    simp only [acfProd, Nat.cast_zero, add_zero, sq]
  rw [Finset.sum_congr rfl hprod, ← Finset.range_eq_Ico]
  field_simp
  ring

/-- **`γ̂(0) →p σ²`**: the second-moment LLN plus the vanishing sample mean. -/
private lemma tendstoInProb_sampleACVF_zero [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (hσ : 0 < σ2) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤
        |sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) 0 - σ2|}).toReal)
      atTop (𝓝 0) := by
  classical
  have hmean : ∀ T : ℕ, 1 ≤ T →
      (μ {ω | η / 2 ≤ ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2}).toReal
        ≤ 2 * σ2 / (η * T) := by
    intro T hT
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hint : Integrable
        (fun ω => ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2) μ := by
      have hsq : Integrable (fun ω => (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2) μ :=
        (memLp_two_iff_integrable_sq
          (memLp_noiseFinsetSum hiid _).aestronglyMeasurable).1 (memLp_noiseFinsetSum hiid _)
      have hcongr : (fun ω => ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2)
          = fun ω => ((T : ℝ)⁻¹) ^ 2 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 := by
        funext ω; rw [mul_pow]
      rw [hcongr]
      exact hsq.const_mul _
    have hmk := markov_toReal (f := fun ω =>
      ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2)
      (fun ω => sq_nonneg _) hint (c := η / 2) (by positivity)
    have hval : ∫ ω, ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 ∂μ = σ2 / T := by
      have hcongr : (fun ω => ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2)
          = fun ω => ((T : ℝ)⁻¹) ^ 2 * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 := by
        funext ω; rw [mul_pow]
      rw [hcongr, integral_const_mul, integral_noiseFinsetSum_sq hiid]
      simp only [Finset.card_range]
      field_simp
    rw [hval] at hmk
    have hEq : σ2 / T / (η / 2) = 2 * σ2 / (η * T) := by
      field_simp
    rw [hEq] at hmk
    exact hmk
  have hmeanlim : Tendsto (fun T : ℕ => 2 * σ2 / (η * T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => η * (T : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hη tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
  have hmean0 : Tendsto (fun T : ℕ =>
      (μ {ω | η / 2 ≤ ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2}).toReal)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hmeanlim
    · filter_upwards with T
      exact ENNReal.toReal_nonneg
    · filter_upwards [eventually_ge_atTop 1] with T hT
      exact hmean T hT
  have hLLN := avgSq_noise_tendstoInProb hiid (show (0:ℝ) < η / 2 by linarith)
  have hbound : ∀ T : ℕ, 1 ≤ T →
      (μ {ω | η ≤ |sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) 0 - σ2|}).toReal
        ≤ (μ {ω | η / 2 ≤ |(T : ℝ)⁻¹ *
              ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2 - σ2|}).toReal
          + (μ {ω | η / 2 ≤
              ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2}).toReal := by
    intro T hT
    have hsub : {ω | η ≤ |sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) 0 - σ2|}
        ⊆ {ω | η / 2 ≤ |(T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2 - σ2|}
          ∪ {ω | η / 2 ≤ ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [Set.mem_setOf_eq, sampleACVF_zero_eq T hT ω] at hω
      have h3 : |(T : ℝ)⁻¹ * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2)
          - ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 - σ2|
          ≤ |(T : ℝ)⁻¹ * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2) - σ2|
            + ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 := by
        have := abs_sub ((T : ℝ)⁻¹ * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2) - σ2)
          (((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2)
        have habs2 : |((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2|
            = ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 :=
          abs_of_nonneg (sq_nonneg _)
        have hre : (T : ℝ)⁻¹ * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2)
            - ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 - σ2
            = ((T : ℝ)⁻¹ * (∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2) - σ2)
              - ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2 := by ring
        rw [hre]
        linarith [habs2.le, habs2.ge]
      linarith
    exact le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))
      (by
        have h4 : μ ({ω | η / 2 ≤ |(T : ℝ)⁻¹ *
              ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω ^ 2 - σ2|}
            ∪ {ω | η / 2 ≤ ((T : ℝ)⁻¹ * ∑ i ∈ Finset.range T, ε ((i : ℤ) + 1) ω) ^ 2})
            ≤ _ + _ := measure_union_le _ _
        calc (μ (_ ∪ _)).toReal
            ≤ (_ + _ : ENNReal).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h4
          _ = _ := ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _))
  refine squeeze_zero' ?_ ?_ (by simpa using hLLN.add hmean0)
  · filter_upwards with T
    exact ENNReal.toReal_nonneg
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact hbound T hT

end Assembly

section Final

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

private lemma memLp_scaledCross [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    MemLp (fun ω => (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) 2 μ :=
  (memLp_finset_sum _ fun i _ => memLp_acfProd hiid hk i).const_mul _

private lemma integral_scaledCross_sq_le [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (hσ : 0 < σ2) {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    ∫ ω, ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) ^ 2 ∂μ ≤ σ2 * σ2 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    positivity
  · have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hpow : ((Real.sqrt (T : ℝ))⁻¹) ^ 2 = ((T : ℝ))⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hTpos.le]
    have hcongr : (fun ω => ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) ^ 2)
        = fun ω => ((T : ℝ))⁻¹ * (∑ i ∈ Finset.range T, acfProd ε k i ω) ^ 2 := by
      funext ω
      rw [mul_pow, hpow]
    rw [hcongr, integral_const_mul, integral_crossSum_sq hiid hk]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hTpos), one_mul]

/-- **RESIDUE (A), CLOSED — the white-noise sample-ACF CLT under two moments.** -/
private theorem sampleACF_whiteNoise_clt [IsProbabilityMeasure μ] (hiid : IsIIDNoise ε σ2 μ)
    (hσ : 0 < σ2) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * sampleACF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k) u)
      atTop (𝓝 (charFun (gaussianReal 0 1) u)) := by
  classical
  have hAmeas : ∀ T : ℕ, Measurable
      (fun ω => (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) := fun T =>
    measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_acfProd hiid k i)
  have hAint : ∀ T : ℕ, Integrable
      (fun ω => ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) ^ 2) μ := fun T =>
    (memLp_two_iff_integrable_sq (memLp_scaledCross hiid hk T).aestronglyMeasurable).1
      (memLp_scaledCross hiid hk T)
  -- the `σ⁻²` multiplier acts on the Gaussian scale
  have hgauss : charFun (gaussianReal 0 (Real.toNNReal (σ2 * σ2))) (σ2⁻¹ * u)
      = charFun (gaussianReal 0 1) u := by
    rw [charFun_gaussianReal, charFun_gaussianReal, Real.coe_toNNReal _ (by positivity)]
    congr 1
    have hneC : (σ2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hσ)
    push_cast
    field_simp
    ring
  have hscaled : Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
      σ2⁻¹ * ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω)) u) atTop
      (𝓝 (charFun (gaussianReal 0 1) u)) := by
    rw [← hgauss]
    refine (crossSum_clt hiid hσ hk (σ2⁻¹ * u)).congr fun T => ?_
    exact (charFun_map_mul_comp (hAmeas T).aemeasurable σ2⁻¹ u).symm
  refine tendsto_charFun_of_tendstoInProb_sub₂
    (fun T => measurable_const.mul (hAmeas T))
    (fun T => measurable_const.mul (measurable_sampleACF₂ hiid.measurable k)) hscaled ?_
  intro δ hδ
  have hratio := tendstoInProb_ratio (μ := μ) (σ2 := σ2)
    (A := fun T ω => (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω)
    (Δ := fun T ω => Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
        - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω)
    (D := fun T ω => sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) 0)
    (K := σ2 * σ2 + 1) hσ (by positivity) hAint
    (fun T => le_trans (integral_scaledCross_sq_le hiid hσ hk T) (by linarith))
    (fun δ' hδ' => tendstoInProb_sampleACVF_sub hiid hσ hk hδ')
    (fun η hη => tendstoInProb_sampleACVF_zero hiid hσ hη) hδ
  have hpt : ∀ (T : ℕ) (ω : Ω),
      (((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω)
          + (Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
            - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω))
            / sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) 0
          - ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) / σ2
        = Real.sqrt T * sampleACF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
          - σ2⁻¹ * ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω) := by
    intro T ω
    rw [show ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω)
        + (Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k
          - (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, acfProd ε k i ω)
        = Real.sqrt T * sampleACVF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k from by ring]
    simp only [sampleACF]
    ring
  simp only [hpt] at hratio
  exact hratio

end Final

end S12b
end StatLean.TimeSeries
