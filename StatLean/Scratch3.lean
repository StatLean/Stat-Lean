import StatLean.TimeSeries.Mixing.KernelRegressionCLT

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The truncated conditional variance is `σ_L² = sL L − (mL L)²`. -/
theorem condExp_truncErr_sq [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    {L : ℝ} (hL : 0 < L)
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω)) :
    μ[fun ω => truncErr X e μ L 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => sL L (X 0 ω) - mL L (X 0 ω) ^ 2 := by
  have hmLv' : μ[fun ω => clampAt L (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) := hmLv
  have hsLv' : μ[fun ω => clampAt L (e 0 ω) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => sL L (X 0 ω) := hsLv
  have hle : MeasurableSpace.comap (X 0) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeasX 0).comap_le
  have hmLmeas : Measurable[MeasurableSpace.comap (X 0) inferInstance]
      (fun ω => mL L (X 0 ω)) := (hmLm L).comp (Measurable.of_comap_le le_rfl)
  have hmLsm : StronglyMeasurable[MeasurableSpace.comap (X 0) inferInstance]
      (fun ω => mL L (X 0 ω)) := hmLmeas.stronglyMeasurable
  have hclm : Measurable (fun ω => clampAt L (e 0 ω)) :=
    (measurable_clampAt L).comp (hmeasE 0)
  have hclb : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  have hci : Integrable (fun ω => clampAt L (e 0 ω)) μ :=
    (integrable_const L).mono' hclm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hclb ω)
  have hcsqi : Integrable (fun ω => clampAt L (e 0 ω) ^ 2) μ :=
    (integrable_const (L ^ 2)).mono' (hclm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hclb ω, abs_nonneg (clampAt L (e 0 ω)), sq_abs (clampAt L (e 0 ω))])
  -- `mL L (X 0 ·)` is a.e. bounded by `L`: it is a version of a conditional expectation
  -- of something bounded by `L`
  have hmLb : ∀ᵐ ω ∂μ, |mL L (X 0 ω)| ≤ L := by
    have hup := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hci
      (integrable_const L) (Eventually.of_forall fun ω => le_trans (le_abs_self _) (hclb ω))
    have hlo := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
      (integrable_const (-L)) hci
      (Eventually.of_forall fun ω => by have := hclb ω; rw [abs_le] at this; exact this.1)
    rw [condExp_const hle L] at hup
    rw [condExp_const hle (-L)] at hlo
    filter_upwards [hup, hlo, hmLv'] with ω h1 h2 h3
    rw [h3] at h1 h2
    rw [abs_le]
    exact ⟨h2, h1⟩
  have hmixi : Integrable (fun ω => mL L (X 0 ω) * clampAt L (e 0 ω)) μ := by
    refine (integrable_const (L * L)).mono'
      (((hmLm L).comp (hmeasX 0)).mul hclm).aestronglyMeasurable ?_
    filter_upwards [hmLb] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hω (hclb ω) (abs_nonneg _) hL.le
  have hmsqi : Integrable (fun ω => mL L (X 0 ω) ^ 2) μ := by
    refine (integrable_const (L * L)).mono'
      (((hmLm L).comp (hmeasX 0)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hmLb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (mL L (X 0 ω)), sq_abs (mL L (X 0 ω))]
  -- expand the square
  have hrep : (fun ω => truncErr X e μ L 0 ω ^ 2)
      =ᵐ[μ] fun ω => clampAt L (e 0 ω) ^ 2
        - 2 * (mL L (X 0 ω) * clampAt L (e 0 ω)) + mL L (X 0 ω) ^ 2 := by
    filter_upwards [hmLv'] with ω hω
    simp only [truncErr]
    rw [show (μ[fun ω' => clampAt L (e 0 ω') |
      MeasurableSpace.comap (X 0) inferInstance]) ω = mL L (X 0 ω) from hω]
    ring
  have hcongr := condExp_congr_ae (m := MeasurableSpace.comap (X 0) inferInstance) hrep
  have h1 : μ[fun ω => clampAt L (e 0 ω) ^ 2
        - 2 * (mL L (X 0 ω) * clampAt L (e 0 ω)) |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => (μ[fun ω' => clampAt L (e 0 ω') ^ 2 |
          MeasurableSpace.comap (X 0) inferInstance]) ω
        - (μ[fun ω' => 2 * (mL L (X 0 ω') * clampAt L (e 0 ω')) |
          MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_sub hcsqi (hmixi.const_mul 2) _
  have h2 : μ[fun ω => (clampAt L (e 0 ω) ^ 2
          - 2 * (mL L (X 0 ω) * clampAt L (e 0 ω))) + mL L (X 0 ω) ^ 2 |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => (μ[fun ω' => clampAt L (e 0 ω') ^ 2
          - 2 * (mL L (X 0 ω') * clampAt L (e 0 ω')) |
          MeasurableSpace.comap (X 0) inferInstance]) ω
        + (μ[fun ω' => mL L (X 0 ω') ^ 2 |
          MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_add (hcsqi.sub (hmixi.const_mul 2)) hmsqi _
  have h3 : μ[fun ω => 2 * (mL L (X 0 ω) * clampAt L (e 0 ω)) |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => 2 * (μ[fun ω' => mL L (X 0 ω') * clampAt L (e 0 ω') |
        MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_smul (𝕜 := ℝ) 2 (fun ω => mL L (X 0 ω) * clampAt L (e 0 ω))
      (MeasurableSpace.comap (X 0) inferInstance)
  have hpull : μ[fun ω => mL L (X 0 ω) * clampAt L (e 0 ω) |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) * (μ[fun ω' => clampAt L (e 0 ω') |
        MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_mul_of_stronglyMeasurable_left hmLsm hmixi hci
  have hself : μ[fun ω => mL L (X 0 ω) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) ^ 2 := by
    rw [condExp_of_stronglyMeasurable hle (hmLmeas.pow_const 2).stronglyMeasurable hmsqi]
  filter_upwards [hcongr, h1, h2, h3, hpull, hself, hmLv', hsLv'] with ω k0 k1 k2 k3 k4 k5 k6 k7
  rw [k0, k2, k1, k3, k4, k5, k6, k7]
  ring

/-- A version of `E(clamp_L e_0 | X_0)` is bounded by `L`. -/
theorem ae_abs_mL_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (mL : ℝ → ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω)) :
    ∀ᵐ ω ∂μ, |mL L (X 0 ω)| ≤ L := by
  have hmLv' : μ[fun ω => clampAt L (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) := hmLv
  have hle : MeasurableSpace.comap (X 0) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeasX 0).comap_le
  have hclm : Measurable (fun ω => clampAt L (e 0 ω)) :=
    (measurable_clampAt L).comp (hmeasE 0)
  have hclb : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  have hci : Integrable (fun ω => clampAt L (e 0 ω)) μ :=
    (integrable_const L).mono' hclm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hclb ω)
  have hup := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hci
    (integrable_const L) (Eventually.of_forall fun ω => le_trans (le_abs_self _) (hclb ω))
  have hlo := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
    (integrable_const (-L)) hci
    (Eventually.of_forall fun ω => by have := hclb ω; rw [abs_le] at this; exact this.1)
  rw [condExp_const hle L] at hup
  rw [condExp_const hle (-L)] at hlo
  filter_upwards [hup, hlo, hmLv'] with ω h1 h2 h3
  rw [h3] at h1 h2
  rw [abs_le]
  exact ⟨h2, h1⟩

/-- The truncated statistic is `clamp_L(e_0) − mL L (X_0)` a.e., hence bounded by `2L`. -/
theorem truncErr_zero_repr [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (mL : ℝ → ℝ → ℝ) {L : ℝ}
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω)) :
    truncErr X e μ L 0 =ᵐ[μ] fun ω => clampAt L (e 0 ω) - mL L (X 0 ω) := by
  have hmLv' : μ[fun ω => clampAt L (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) := hmLv
  filter_upwards [hmLv'] with ω hω
  simp only [truncErr]
  rw [show (μ[fun ω' => clampAt L (e 0 ω') |
    MeasurableSpace.comap (X 0) inferInstance]) ω = mL L (X 0 ω) from hω]

/-- **The truncated diagonal (2.73)-for-`e^L`.** -/
theorem tendsto_truncDiag [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {p : ℝ → ℝ} {x : ℝ}
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L)) (hsLm : ∀ L : ℝ, Measurable (sL L))
    {L : ℝ} (hL : 0 < L)
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (h n)⁻¹ *
        ∫ ω, truncErr X e μ L 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
  have hle : MeasurableSpace.comap (X 0) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeasX 0).comap_le
  have hmLb := ae_abs_mL_le hmeasX hmeasE mL hL hmLv
  have hrep := truncErr_zero_repr (X := X) (e := e) mL hmLv
  have hclm : Measurable (fun ω => clampAt L (e 0 ω)) :=
    (measurable_clampAt L).comp (hmeasE 0)
  have hclb : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  -- `σ_L²` is continuous at `x`, because `σ_L²·p` is and `p x > 0`
  have hpne : ∀ᶠ v in 𝓝 x, 0 < p v := hpc.eventually (eventually_gt_nhds hpx)
  have hσc : ContinuousAt (fun v => sL L v - mL L v ^ 2) x := by
    refine ContinuousAt.congr (hσLc.div hpc hpx.ne') ?_
    filter_upwards [hpne] with v hv
    simp only [Pi.div_apply]
    field_simp
  -- integrability of the truncated square
  have htm : AEStronglyMeasurable (truncErr X e μ L 0) μ :=
    (hclm.sub ((hmLm L).comp (hmeasX 0))).aestronglyMeasurable.congr hrep.symm
  have he2 : Integrable (fun ω => truncErr X e μ L 0 ω ^ 2) μ := by
    refine (integrable_const ((2 * L) ^ 2)).mono' (htm.pow 2) ?_
    filter_upwards [hrep, hmLb] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), h1]
    have hb : |clampAt L (e 0 ω) - mL L (X 0 ω)| ≤ 2 * L := by
      have := hclb ω
      rw [abs_le] at this h2 ⊢
      constructor <;> linarith [this.1, this.2, h2.1, h2.2]
    nlinarith [abs_nonneg (clampAt L (e 0 ω) - mL L (X 0 ω)),
      sq_abs (clampAt L (e 0 ω) - mL L (X 0 ω)), hL.le]
  exact tendsto_localized_second_moment_debt (X := X) (e := fun _ => truncErr X e μ L 0)
    (hmeasX 0) ((hsLm L).sub ((hmLm L).pow_const 2)) hmp hp0 hpd
    (condExp_truncErr_sq hmeasX hmeasE mL sL hmLm hL hmLv hsLv) he2 hσc hpc hσLb hWm hWb hW2
    hh0 hh

/-- Sub-diagonal form of `abs_double_sum_subset_le`. -/
theorem abs_double_sum_subset_sub_diag_le {n : ℕ} (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hc : ∀ s d : ℕ, c s (s + d) = g d) (hc' : ∀ s d : ℕ, c (s + d) s = g d) :
    |(∑ s ∈ I, ∑ t ∈ I, c s t) - (I.card : ℝ) * g 0|
      ≤ (I.card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := by
  classical
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 n, |g j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hdiag : ∀ s : ℕ, c s s = g 0 := fun s => by simpa using hc s 0
  have key : ∀ s ∈ I, |(∑ t ∈ I, c s t) - g 0| ≤ 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by
    intro s hs
    have hsn : s < n := Finset.mem_range.1 (hI hs)
    have hsplit : (∑ t ∈ I, c s t) - g 0 = ∑ t ∈ I.erase s, c s t := by
      rw [← Finset.add_sum_erase _ _ hs, hdiag]; ring
    set A : Finset ℕ := I.filter (fun t => t < s) with hA
    set B : Finset ℕ := I.filter (fun t => s < t) with hB
    have hAB : I.erase s = A ∪ B := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_union, hA, hB, Finset.mem_filter]
      constructor
      · rintro ⟨hts, htI⟩; rcases lt_or_gt_of_ne hts with h | h
        · exact Or.inl ⟨htI, h⟩
        · exact Or.inr ⟨htI, h⟩
      · rintro (⟨htI, h⟩ | ⟨htI, h⟩) <;> exact ⟨by omega, htI⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro t htA htB
      simp only [hA, hB, Finset.mem_filter] at htA htB
      omega
    rw [hsplit]
    calc |∑ t ∈ I.erase s, c s t|
        ≤ ∑ t ∈ I.erase s, |c s t| := Finset.abs_sum_le_sum_abs _ _
      _ = (∑ t ∈ A, |c s t|) + ∑ t ∈ B, |c s t| := by
          rw [hAB, Finset.sum_union hdisj]
      _ ≤ (∑ j ∈ Finset.Ico 1 n, |g j|) + ∑ j ∈ Finset.Ico 1 n, |g j| := by
          gcongr
          · have hinj : ∀ t₁ ∈ A, ∀ t₂ ∈ A, s - t₁ = s - t₂ → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hA, Finset.mem_filter] at h₁ h₂
              omega
            have himg : A.image (fun t => s - t) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hA, Finset.mem_filter] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
              simp only [Finset.mem_Ico]
              omega
            have hval : ∀ t ∈ A, |c s t| = |g (s - t)| := by
              intro t ht
              simp only [hA, Finset.mem_filter] at ht
              have : t + (s - t) = s := by omega
              rw [← hc' t (s - t), this]
            have himgsum : ∑ j ∈ A.image (fun t => s - t), |g j| = ∑ t ∈ A, |g (s - t)| :=
              Finset.sum_image hinj
            rw [Finset.sum_congr rfl hval, ← himgsum]
            exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => abs_nonneg _
          · have hinj : ∀ t₁ ∈ B, ∀ t₂ ∈ B, t₁ - s = t₂ - s → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hB, Finset.mem_filter] at h₁ h₂
              omega
            have himg : B.image (fun t => t - s) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hB, Finset.mem_filter] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
              have : t < n := Finset.mem_range.1 (hI ht1)
              simp only [Finset.mem_Ico]
              omega
            have hval : ∀ t ∈ B, |c s t| = |g (t - s)| := by
              intro t ht
              simp only [hB, Finset.mem_filter] at ht
              have : s + (t - s) = t := by omega
              rw [← hc s (t - s), this]
            have himgsum : ∑ j ∈ B.image (fun t => t - s), |g j| = ∑ t ∈ B, |g (t - s)| :=
              Finset.sum_image hinj
            rw [Finset.sum_congr rfl hval, ← himgsum]
            exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => abs_nonneg _
      _ = 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by ring
  have hrw : (∑ s ∈ I, ∑ t ∈ I, c s t) - (I.card : ℝ) * g 0
      = ∑ s ∈ I, ((∑ t ∈ I, c s t) - g 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hrw]
  calc |∑ s ∈ I, ((∑ t ∈ I, c s t) - g 0)|
      ≤ ∑ s ∈ I, |(∑ t ∈ I, c s t) - g 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ I, (2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := Finset.sum_le_sum key
    _ = (I.card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := by
        rw [Finset.sum_const, nsmul_eq_mul]

set_option maxHeartbeats 2000000 in
theorem tendsto_truncArray_variance [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L)
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    (I : ℕ → Finset ℕ) (hIsub : ∀ n, I n ⊆ Finset.range n) {a : ℝ}
    (hIcard : Tendsto (fun n : ℕ => ((I n).card : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ) atTop
      (𝓝 (a * ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2))) := by
  classical
  obtain ⟨mm, hmmM, hmmB, hmrep⟩ := exists_truncErr_repr hmeasX hmeasE hstat hL
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) := (Real.continuous_rpow_const hδ0.le).measurable
  -- `|W|^δ` is integrable
  have hWam : Measurable (fun v => |W v| ^ δ) := hrp.comp hWm.abs
  have hWδ : Integrable (fun v => |W v| ^ δ) MeasureTheory.volume := by
    refine Integrable.mono (hW2.const_mul (CW ^ (δ - 2))) hWam.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    have hsplit : |W v| ^ δ = |W v| ^ (δ - 2) * |W v| ^ (2 : ℝ) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by intro hcon; linarith),
        show δ - 2 + 2 = δ from by ring]
    have h2 : |W v| ^ (2 : ℝ) = W v ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    have hle : |W v| ^ (δ - 2) ≤ CW ^ (δ - 2) :=
      Real.rpow_le_rpow (abs_nonneg _) (hWb v) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hsplit, h2,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ (δ - 2) * W v ^ 2)]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  -- the pair function and the truncated array
  set F : ℕ → ℝ × ℝ → ℝ := fun n z => (clampAt L z.2 - mm z.1) * W ((z.1 - x) / h n) with hFdef
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact (((measurable_clampAt L).comp measurable_snd).sub (hmmM.comp measurable_fst)).mul
      (hWm.comp ((measurable_fst.sub measurable_const).div measurable_const))
  have hbase : ∀ z : ℝ × ℝ, |clampAt L z.2 - mm z.1| ≤ 2 * L := by
    intro z
    have ha := abs_le.1 (abs_clampAt_le hL.le z.2)
    have hb := abs_le.1 (hmmB z.1)
    rw [abs_le]; constructor <;> linarith
  have hFb : ∀ (n : ℕ) (z : ℝ × ℝ), |F n z| ≤ 2 * L * CW := by
    intro n z
    have h1 := hbase z
    have h2 := hWb ((z.1 - x) / h n)
    simp only [hFdef, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hL.le])
  set Z : ℕ → ℤ → Ω → ℝ := fun n t ω => F n (X t ω, e t ω) with hZdef
  have hZm : ∀ (n : ℕ) (t : ℤ), Measurable (Z n t) := fun n t =>
    (hFm n).comp ((hmeasX t).prodMk (hmeasE t))
  have hZb : ∀ (n : ℕ) (t : ℤ) (ω : Ω), |Z n t ω| ≤ 2 * L * CW := fun n t ω => hFb n _
  have hZmem : ∀ (n : ℕ) (t : ℤ) (q : ℝ≥0∞), MemLp (Z n t) q μ := fun n t q =>
    MemLp.of_bound (hZm n t).aestronglyMeasurable (2 * L * CW)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb n t ω)
  have hint : ∀ (n : ℕ) (s t : ℤ), Integrable (fun ω => Z n s ω * Z n t ω) μ :=
    fun n s t => (hZmem n s 2).integrable_mul (hZmem n t 2)
  have hZrep : ∀ (n : ℕ) (t : ℤ),
      (fun ω => truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] Z n t := by
    intro n t
    filter_upwards [hmrep t] with ω hω
    simp only [hZdef, hFdef, hω]
  -- each summand is centred
  have hclampint : ∀ t : ℤ, Integrable (fun ω => clampAt L (e t ω)) μ := by
    intro t
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE t)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL.le _
  have hcond : ∀ t : ℤ,
      μ[fun ω => clampAt L (e t ω) | MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => mm (X t ω) := by
    intro t
    filter_upwards [hmrep t] with ω hω
    simp only [truncErr] at hω
    linarith
  have hmean0 : ∀ (n : ℕ) (t : ℤ), ∫ ω, Z n t ω ∂μ = 0 := by
    intro n t
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX t) (hclampint t) (hcond t)
      (fun v => W ((v - x) / h n)) (by fun_prop) (C := CW) (fun v => hWb _)
    have hi1 : Integrable (fun ω => W ((X t ω - x) / h n) * clampAt L (e t ω)) μ :=
      (hclampint t).bdd_mul
        ((hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb _)
    have hi2 : Integrable (fun ω => W ((X t ω - x) / h n) * mm (X t ω)) μ := by
      refine (integrable_const (CW * L)).mono'
        (((hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)).mul
          (hmmM.comp (hmeasX t))).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWb _) (hmmB _) (abs_nonneg _) hCW0
    have hsplit : ∫ ω, Z n t ω ∂μ
        = ∫ ω, W ((X t ω - x) / h n) * clampAt L (e t ω) ∂μ
          - ∫ ω, W ((X t ω - x) / h n) * mm (X t ω) ∂μ := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [hZdef, hFdef]; ring)
    rw [hsplit, hz, sub_self]
  -- the lag covariance array
  set Gz : ℕ → ℕ → ℝ := fun n d => ∫ ω, Z n 0 ω * Z n (d : ℤ) ω ∂μ with hGzdef
  set Cz : ℕ → ℕ → ℕ → ℝ := fun n s t => ∫ ω, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω ∂μ
    with hCzdef
  have hCG : ∀ n s d : ℕ, Cz n s (s + d) = Gz n d := by
    intro n s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr := integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
      (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) => F n z.1 * F n z.2)
      (((hFm n).comp measurable_fst).mul ((hFm n).comp measurable_snd))
    simp only [hCzdef, hGzdef, hZdef, hidx]
    exact htr
  have hCG' : ∀ n s d : ℕ, Cz n (s + d) s = Gz n d := by
    intro n s d
    have hsym : Cz n (s + d) s = Cz n s (s + d) := by
      simp only [hCzdef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  -- the sum of squares expands
  have hexp : ∀ n : ℕ, ∫ ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = ∑ s ∈ I n, ∑ t ∈ I n, Cz n s t := by
    intro n
    have hsq : ∀ ω : Ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2
        = ∑ s ∈ I n, ∑ t ∈ I n, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp only [hsq, hCzdef]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hint n _ _))]
    exact Finset.sum_congr rfl fun s _ =>
      integral_finset_sum _ (fun t _ => hint n _ _)
  -- diagonal
  have hdiag : ∀ n : ℕ, |Gz n 0| ≤ (4 * L ^ 2) * ((Cp * ∫ v, W v ^ 2) * h n) := by
    intro n
    have hWsqm : Measurable (fun ω => W ((X 0 ω - x) / h n) ^ 2) :=
      (hWm.comp (((hmeasX 0).sub measurable_const).div measurable_const)).pow_const 2
    have hGeq : Gz n 0 = ∫ ω, (Z n 0 ω) ^ 2 ∂μ := by
      simp only [hGzdef, Nat.cast_zero]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hnn : 0 ≤ Gz n 0 := by
      rw [hGeq]; exact integral_nonneg fun ω => sq_nonneg _
    have hi2 : Integrable (fun ω => 4 * L ^ 2 * W ((X 0 ω - x) / h n) ^ 2) μ := by
      refine (integrable_const (4 * L ^ 2 * CW ^ 2)).mono'
        (hWsqm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb := hWb ((X 0 ω - x) / h n)
      have habs := abs_nonneg (W ((X 0 ω - x) / h n))
      have hsq : W ((X 0 ω - x) / h n) ^ 2 ≤ CW ^ 2 := by
        nlinarith [sq_abs (W ((X 0 ω - x) / h n))]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have hstep : ∫ ω, (Z n 0 ω) ^ 2 ∂μ ≤ (4 * L ^ 2) * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono (hZmem n 0 2).integrable_sq hi2 fun ω => ?_
      have hb := hbase (X 0 ω, e 0 ω)
      have hsq : (clampAt L (e 0 ω) - mm (X 0 ω)) ^ 2 ≤ 4 * L ^ 2 := by
        nlinarith [abs_nonneg (clampAt L (e 0 ω) - mm (X 0 ω)),
          sq_abs (clampAt L (e 0 ω) - mm (X 0 ω)), hL.le]
      simp only [hZdef, hFdef, mul_pow]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hloc := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => W v ^ 2) (hWm.pow_const 2) (fun v => sq_nonneg _) hW2 (x := x) (hh0 n)
    rw [abs_of_nonneg hnn, hGeq]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_left hloc (by positivity)
  -- small lags
  have hIW0 : (0 : ℝ) ≤ ∫ v, |W v| := integral_nonneg fun v => abs_nonneg _
  have hsmall : ∀ (n j : ℕ), 1 ≤ j →
      |Gz n j| ≤ (4 * L ^ 2) * (B * ((∫ v, |W v|) * h n) ^ 2) := by
    intro n j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    have hgm : Measurable (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|) := by
      fun_prop
    have hg0 : ∀ z : ℝ × ℝ, 0 ≤ |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)| :=
      fun z => by positivity
    have hgXm : Measurable (fun ω => |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) :=
      hgm.comp ((hmeasX 0).prodMk (hmeasX (j : ℤ)))
    have hgi : Integrable
        (fun ω => 4 * L ^ 2 * (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|)) μ := by
      refine (integrable_const (4 * L ^ 2 * (CW * CW))).mono'
        (hgXm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hWb ((X 0 ω - x) / h n)
      have h2 := hWb ((X (j : ℤ) ω - x) / h n)
      have h3 : |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ≤ CW * CW :=
        mul_le_mul h1 h2 (abs_nonneg _) hCW0
      nlinarith [sq_nonneg L]
    have hA : |Gz n j| ≤ (4 * L ^ 2) *
        ∫ ω, |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ∂μ := by
      have h0 := norm_integral_le_integral_norm (μ := μ) (fun ω => Z n 0 ω * Z n (j : ℤ) ω)
      simp only [Real.norm_eq_abs] at h0
      refine (le_trans h0 ?_)
      rw [← integral_const_mul]
      refine integral_mono (hint n 0 (j : ℤ)).abs hgi fun ω => ?_
      have hb0 := hbase (X 0 ω, e 0 ω)
      have hbj := hbase (X (j : ℤ) ω, e (j : ℤ) ω)
      simp only [hZdef, hFdef, abs_mul]
      have hL2 : (0 : ℝ) ≤ 2 * L := by linarith
      calc |clampAt L (e 0 ω) - mm (X 0 ω)| * |W ((X 0 ω - x) / h n)| *
              (|clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω)| * |W ((X (j : ℤ) ω - x) / h n)|)
          = (|clampAt L (e 0 ω) - mm (X 0 ω)| *
              |clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω)|) *
              (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by ring
        _ ≤ (4 * L ^ 2) * (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [abs_nonneg (clampAt L (e 0 ω) - mm (X 0 ω)),
              abs_nonneg (clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω))]
    have hC2 := hC2gen (j : ℤ) hjz (fun _ => (1 : ℝ)) measurable_const _ hgm hg0
    have hone : ∫ ω, |(fun _ : ℝ × ℝ => (1 : ℝ)) (e 0 ω, e (j : ℤ) ω)| ∂μ = 1 := by
      simp
    have hlhs : ∫ ω, |(fun _ : ℝ × ℝ => (1 : ℝ)) (e 0 ω, e (j : ℤ) ω)| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
            (X 0 ω, X (j : ℤ) ω) ∂μ
        = ∫ ω, |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ∂μ := by
      simp
    rw [hone, hlhs, mul_one] at hC2
    have hprod : ∫ z : ℝ × ℝ, |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|
          ∂(MeasureTheory.volume.prod MeasureTheory.volume)
        = (∫ v, |W ((v - x) / h n)|) * ∫ w, |W ((w - x) / h n)| :=
      integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (f := fun v => |W ((v - x) / h n)|) (g := fun w => |W ((w - x) / h n)|)
    have honeW : ∫ v, |W ((v - x) / h n)| = h n * ∫ v, |W v| := by
      have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x (hh0 n)
      simp only [mul_one] at this
      rw [this, ← mul_assoc, mul_inv_cancel₀ (hh0 n).ne', one_mul]
    rw [hprod, honeW] at hC2
    refine hA.trans ?_
    refine mul_le_mul_of_nonneg_left (hC2.trans (le_of_eq ?_)) (by positivity)
    ring
  -- the localized δ-th moment of the truncated array
  have hIWδ0 : (0 : ℝ) ≤ ∫ v, |W v| ^ δ :=
    integral_nonneg fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hKzbd : ∀ n : ℕ,
      ∫ ω, |Z n 0 ω| ^ δ ∂μ ≤ ((2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ)) * h n := by
    intro n
    have hGm : Measurable (fun v => |W ((v - x) / h n)| ^ δ) :=
      hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
    have hGXm : Measurable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) := hGm.comp (hmeasX 0)
    have hdom : ∀ ω, |Z n 0 ω| ^ δ ≤ (2 * L) ^ δ * |W ((X 0 ω - x) / h n)| ^ δ := by
      intro ω
      simp only [hZdef, hFdef, abs_mul]
      rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      have h1 : |clampAt L (e 0 ω) - mm (X 0 ω)| ^ δ ≤ (2 * L) ^ δ :=
        Real.rpow_le_rpow (abs_nonneg _) (hbase (X 0 ω, e 0 ω)) hδ0.le
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg _) _)
    have hi1 : Integrable (fun ω => |Z n 0 ω| ^ δ) μ := by
      refine (integrable_const ((2 * L * CW) ^ δ)).mono'
        ((hrp.comp (hZm n 0).abs)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hZb n 0 ω) hδ0.le
    have hi2 : Integrable (fun ω => (2 * L) ^ δ * |W ((X 0 ω - x) / h n)| ^ δ) μ := by
      refine (integrable_const ((2 * L) ^ δ * CW ^ δ)).mono'
        (hGXm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le) (Real.rpow_nonneg (by linarith) _)
    have hstep : ∫ ω, |Z n 0 ω| ^ δ ∂μ
        ≤ (2 * L) ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono hi1 hi2 hdom
    have hloc := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => |W v| ^ δ) hWam (fun v => Real.rpow_nonneg (abs_nonneg _) _) hWδ
      (x := x) (hh0 n)
    refine hstep.trans ?_
    calc (2 * L) ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
        ≤ (2 * L) ^ δ * ((Cp * ∫ v, |W v| ^ δ) * h n) :=
          mul_le_mul_of_nonneg_left hloc (Real.rpow_nonneg (by linarith) _)
      _ = ((2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ)) * h n := by ring
  -- the δ-norms of the truncated array, and Davydov
  set Kz : ℝ := (2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ) with hKzdef
  have hKz0 : (0 : ℝ) ≤ Kz :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (mul_nonneg hCp0 hIWδ0)
  have hnormδ : ∀ (n : ℕ) (t : ℤ),
      (eLpNorm (Z n t) (ENNReal.ofReal δ) μ).toReal ≤ (Kz * h n) ^ (1 / δ) := by
    intro n t
    have hEq : eLpNorm (Z n t) (ENNReal.ofReal δ) μ = eLpNorm (Z n 0) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t (hFm n) _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := (hZmem n 0 (ENNReal.ofReal δ)).eLpNorm_eq_integral_rpow_norm hp1
      ENNReal.ofReal_ne_top
    have hb0 : (0 : ℝ) ≤ ∫ a, ‖Z n 0 a‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hb0 _), ← one_div]
    have hnn : ∫ a, ‖Z n 0 a‖ ^ δ ∂μ ≤ Kz * h n := by
      simpa only [Real.norm_eq_abs] using hKzbd n
    exact Real.rpow_le_rpow hb0 hnn (by positivity)
  have hlarge : ∀ (n j : ℕ), 1 ≤ j →
      |Gz n j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kz * h n) ^ (2 / δ) := by
    intro n j hj
    have hcov : cov[Z n 0, Z n (j : ℤ); μ] = Gz n j := by
      rw [covariance_eq_sub (hZmem n 0 2) (hZmem n (j : ℤ) 2), hmean0 n 0, zero_mul, sub_zero]
      simp only [hGzdef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound' hmeasX hmeasE hδ (hFm n) j hj
      (hZmem n 0 (ENNReal.ofReal δ)) (hZmem n (j : ℤ) (ENNReal.ofReal δ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ Kz * h n := mul_nonneg hKz0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (Kz * h n) ^ (2 / δ) = (Kz * h n) ^ (1 / δ) * (Kz * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδ n 0
    · exact hnormδ n (j : ℤ)
  -- the lag sum, split at `m_n`
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  have hsplit : ∀ n : ℕ, 1 ≤ smallLagCut h n →
      ∑ j ∈ Finset.Ico 1 n, |Gz n j|
        ≤ (smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2))
          + 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    intro n hm1
    have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gz n j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gz n j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gz n j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gz n j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gz n j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gz n j|
        ≤ (smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2)) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gz n j|) ((4 * L ^ 2) * (B * (IW * h n) ^ 2))
        (fun j hj => hsmall n j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gz n j|
        ≤ 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (Kz * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hKz0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gz n j| ≤ 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
            ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
        have hj1' : 1 ≤ j := by omega
        refine (hlarge n j hj1').trans ?_
        have hmj : (smallLagCut h n : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
          Real.rpow_le_rpow hmR.le (by exact_mod_cast (by omega : smallLagCut h n ≤ j)) hlam0.le
        have hαβ : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
          Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
        have hid : (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam = 1 := by
          rw [← Real.rpow_add hmR]; simp
        have hge1 : (1 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam := by
          calc (1 : ℝ) = (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam := hid.symm
            _ ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam :=
                mul_le_mul_of_nonneg_left hmj hmneg
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kz * h n) ^ (2 / δ)
            = 8 * (Kz * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (Kz * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by gcongr
          _ = 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  have hRto0 : Tendsto (fun n : ℕ => 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (2 * (4 * L ^ 2) * B * IW ^ 2) * ((smallLagCut h n : ℝ) * h n)
          + (16 * SA * Kz ^ (2 / δ)) *
            (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam)) atTop (𝓝 0) := by
      have t1 := (tendsto_smallLagCut_mul_bandwidth hh0 hh).const_mul
        (2 * (4 * L ^ 2) * B * IW ^ 2)
      have t2 := (tendsto_rpow_mul_abs_log_rpow hh0 hh (a := 2 / δ - 1 + lam)
        (by linarith) hlam0).const_mul (16 * SA * Kz ^ (2 / δ))
      simpa using t1.add t2
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards with n
      have hhn := hh0 n
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    · filter_upwards [(tendsto_abs_log_atTop hh0 hh).eventually_gt_atTop 0] with n hLn
      have hhn : 0 < h n := hh0 n
      have hposL : (0 : ℝ) < h n * |Real.log (h n)| := by positivity
      have hm1 : 1 ≤ smallLagCut h n := Nat.ceil_pos.2 (by positivity)
      have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
      have hmge : (h n * |Real.log (h n)|)⁻¹ ≤ (smallLagCut h n : ℝ) := Nat.le_ceil _
      have hmlam : (0 : ℝ) < (smallLagCut h n : ℝ) ^ lam := Real.rpow_pos_of_pos hmR _
      have hmb : (smallLagCut h n : ℝ) ^ (-lam) ≤ (h n * |Real.log (h n)|) ^ lam := by
        have hprod1 : (1 : ℝ) ≤ (h n * |Real.log (h n)|) * (smallLagCut h n : ℝ) := by
          have h0 := mul_le_mul_of_nonneg_left hmge hposL.le
          rwa [mul_inv_cancel₀ hposL.ne'] at h0
        have h5 : (1 : ℝ) ≤ ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam := by
          have h5' := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod1 hlam0.le
          rwa [Real.one_rpow] at h5'
        have h6 : ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam
            = (h n * |Real.log (h n)|) ^ lam * (smallLagCut h n : ℝ) ^ lam :=
          Real.mul_rpow hposL.le hmR.le
        rw [Real.rpow_neg hmR.le]
        refine le_of_mul_le_mul_right ?_ hmlam
        rw [inv_mul_cancel₀ hmlam.ne', ← h6]
        exact h5
      have hS := hsplit n hm1
      refine (mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * (h n)⁻¹)).trans ?_
      rw [mul_add]
      have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2)))
          = (2 * (4 * L ^ 2) * B * IW ^ 2) * ((smallLagCut h n : ℝ) * h n) := by
        field_simp
      have hKrw : (Kz * h n) ^ (2 / δ) = Kz ^ (2 / δ) * (h n) ^ (2 / δ) :=
        Real.mul_rpow hKz0 hhn.le
      have hLrw : (h n * |Real.log (h n)|) ^ lam
          = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
      have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
        rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
          Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
      have hKh : (0 : ℝ) ≤ (Kz * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hKz0 hhn.le) _
      have e2 : 2 * (h n)⁻¹ * (8 * (Kz * h n) ^ (2 / δ) *
            ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ (16 * SA * Kz ^ (2 / δ)) *
            ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
        calc 2 * (h n)⁻¹ *
              (8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
            ≤ 2 * (h n)⁻¹ * (8 * (Kz * h n) ^ (2 / δ) *
                ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
          _ = (16 * SA * Kz ^ (2 / δ)) *
                ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
              rw [hKrw, hLrw, hpow]; ring
      linarith
  -- assembly
  have hsumrep : ∀ n : ℕ,
      ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
        = ∫ ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    intro n
    refine integral_congr_ae ?_
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ I n,
        truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          = Z n ((t : ℤ) + 1) ω :=
      (Filter.eventually_all_finset (I n)).2 (fun t _ => hZrep n ((t : ℤ) + 1))
    filter_upwards [hall] with ω hω
    rw [Finset.sum_congr rfl hω]
  -- the diagonal, as the truncated second moment
  have hG0 : ∀ n : ℕ,
      Gz n 0 = ∫ ω, truncErr X e μ L 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
    intro n
    simp only [hGzdef, Nat.cast_zero]
    refine integral_congr_ae ?_
    filter_upwards [hZrep n 0] with ω hω
    rw [← hω]
    ring
  have hdiaglim : Tendsto (fun n : ℕ => (h n)⁻¹ * Gz n 0) atTop
      (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
    simpa only [hG0] using tendsto_truncDiag hmeasX hmeasE hmp hp0 hpd mL sL hmLm hsLm hL
      hmLv hsLv hσLc hσLb hpc hpx hWm hWb hW2 hh0 hh
  have hmain : Tendsto (fun n : ℕ => (((I n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0))
      atTop (𝓝 (a * ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2))) := hIcard.mul hdiaglim
  have herr : Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t)
      - (((I n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (((I n).card : ℝ) / (n : ℝ)) *
        (2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)) atTop (𝓝 0) := by
      simpa using hIcard.mul hRto0
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hhn : 0 < h n := hh0 n
    have habs := abs_double_sum_subset_sub_diag_le (I n) (hIsub n) (Cz n) (Gz n)
      (hCG n) (hCG' n)
    have hid : ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t)
        - (((I n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0)
        = ((n : ℝ) * h n)⁻¹ *
          ((∑ s ∈ I n, ∑ t ∈ I n, Cz n s t) - ((I n).card : ℝ) * Gz n 0) := by
      field_simp
    have hid2 : ((n : ℝ) * h n)⁻¹ *
        (((I n).card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|))
        = (((I n).card : ℝ) / (n : ℝ)) *
          (2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
      field_simp
    rw [Real.norm_eq_abs, hid, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h n)⁻¹), ← hid2]
    exact mul_le_mul_of_nonneg_left habs (by positivity)
  have hconv : ∀ n : ℕ, ((n : ℝ) * h n)⁻¹ *
      ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
        W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
      = ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t) := by
    intro n; rw [hsumrep n, hexp n]
  simp only [hconv]
  have hsum := hmain.add herr
  rw [add_zero] at hsum
  exact hsum.congr fun n => by ring


section Shift

/-- A Borel isomorphism `ℝ × ℝ ≃ᵐ ℝ`, used to encode the pair series as a real series so
that the shift lemma of `Mixing/Relations.lean` applies to it. -/
noncomputable def pairCode : (ℝ × ℝ) ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable
    (Uncountable.not_countable) (Uncountable.not_countable)

/-- The coded pair series generates the same one-time σ-algebras as the pair. -/
theorem comap_pairCode {X e : ℤ → Ω → ℝ} (t : ℤ) :
    MeasurableSpace.comap (fun ω => pairCode (X t ω, e t ω)) inferInstance
      = MeasurableSpace.comap (X t) inferInstance ⊔
        MeasurableSpace.comap (e t) inferInstance := by
  have h1 : MeasurableSpace.comap (fun ω => pairCode (X t ω, e t ω))
      (inferInstance : MeasurableSpace ℝ)
      = MeasurableSpace.comap (fun ω => (X t ω, e t ω))
        (MeasurableSpace.comap pairCode (inferInstance : MeasurableSpace ℝ)) :=
    (MeasurableSpace.comap_comp).symm
  have h2 : MeasurableSpace.comap (pairCode : ℝ × ℝ → ℝ) (inferInstance : MeasurableSpace ℝ)
      = (inferInstance : MeasurableSpace (ℝ × ℝ)) := by
    refine le_antisymm pairCode.measurable.comap_le ?_
    intro s hs
    refine ⟨pairCode.symm ⁻¹' s, pairCode.symm.measurable hs, ?_⟩
    ext z
    simp
  rw [h1, h2]
  show MeasurableSpace.comap (fun ω => (X t ω, e t ω))
      (MeasurableSpace.comap Prod.fst inferInstance ⊔
        MeasurableSpace.comap Prod.snd inferInstance) = _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

/-- Under fdd stationarity of the pair, arbitrary finite tuples of the pair are
shift-invariant in law. -/
theorem map_tuple_shift {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (n : ℕ) (t : Fin n → ℤ) (a : ℤ) :
    μ.map (fun ω (i : Fin n) => (X (t i + a) ω, e (t i + a) ω))
      = μ.map (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω)) := by
  classical
  have hwin : ∀ (m : ℕ) (b : ℤ),
      Measurable (fun ω (i : Fin m) => (X (b + (i : ℕ)) ω, e (b + (i : ℕ)) ω)) :=
    fun m b => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  set M : ℕ := Finset.univ.sup (fun i : Fin n => (t i).natAbs) with hM
  have hMle : ∀ i : Fin n, (t i).natAbs ≤ M := fun i =>
    Finset.le_sup (f := fun i : Fin n => (t i).natAbs) (Finset.mem_univ i)
  have hj : ∀ i : Fin n, (t i + (M : ℤ)).toNat < 2 * M + 1 := by
    intro i; have := hMle i; omega
  set j : Fin n → Fin (2 * M + 1) := fun i => ⟨(t i + (M : ℤ)).toNat, hj i⟩ with hjdef
  set proj : (Fin (2 * M + 1) → ℝ × ℝ) → (Fin n → ℝ × ℝ) := fun z i => z (j i) with hprojdef
  have hprojm : Measurable proj := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hcomp : ∀ b : ℤ, (fun ω (i : Fin n) => (X (t i + b) ω, e (t i + b) ω))
      = proj ∘ (fun ω (i : Fin (2 * M + 1)) =>
          (X ((b - (M : ℤ)) + (i : ℕ)) ω, e ((b - (M : ℤ)) + (i : ℕ)) ω)) := by
    intro b
    funext ω i
    have hval : (b - (M : ℤ)) + (((j i : Fin (2 * M + 1)) : ℕ) : ℤ) = t i + b := by
      simp only [hjdef]
      have := hMle i
      omega
    simp only [hprojdef, Function.comp_apply, hval]
  have h0 : (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω))
      = (fun ω (i : Fin n) => (X (t i + 0) ω, e (t i + 0) ω)) := by simp
  rw [hcomp a, h0, hcomp 0,
    ← Measure.map_map hprojm (hwin (2 * M + 1) (a - (M : ℤ))),
    ← Measure.map_map hprojm (hwin (2 * M + 1) ((0 : ℤ) - (M : ℤ))),
    hstat (2 * M + 1) (a - (M : ℤ)), hstat (2 * M + 1) ((0 : ℤ) - (M : ℤ))]

/-- The coded pair series is strictly stationary. -/
theorem isStrictlyStationary_pairCode {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω))) :
    IsStrictlyStationary (fun t ω => pairCode (X t ω, e t ω)) μ := by
  intro n t k
  have hm : ∀ b : ℤ, Measurable (fun ω (i : Fin n) => (X (t i + b) ω, e (t i + b) ω)) :=
    fun b => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hm0 : Measurable (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω)) :=
    measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hcode : Measurable (fun (z : Fin n → ℝ × ℝ) (i : Fin n) => pairCode (z i)) :=
    measurable_pi_lambda _ fun i => pairCode.measurable.comp (measurable_pi_apply i)
  have e1 : (fun ω (i : Fin n) => pairCode (X (t i + k) ω, e (t i + k) ω))
      = (fun (z : Fin n → ℝ × ℝ) (i : Fin n) => pairCode (z i))
        ∘ (fun ω (i : Fin n) => (X (t i + k) ω, e (t i + k) ω)) := rfl
  have e2 : (fun ω (i : Fin n) => pairCode (X (t i) ω, e (t i) ω))
      = (fun (z : Fin n → ℝ × ℝ) (i : Fin n) => pairCode (z i))
        ∘ (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω)) := rfl
  show μ.map (fun ω (i : Fin n) => pairCode (X (t i + k) ω, e (t i + k) ω))
      = μ.map (fun ω (i : Fin n) => pairCode (X (t i) ω, e (t i) ω))
  rw [e1, e2, ← Measure.map_map hcode (hm k), ← Measure.map_map hcode hm0,
    map_tuple_shift hmeasX hmeasE hstat n t k]

/-- **Shift lemma for the pair series.** Under fdd stationarity the α-coefficient between
the pair past up to `k` and the pair future from `k + d` is `pairAlphaCoeff X e μ d`. -/
theorem pairAlphaCoeff_shift [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (k : ℤ) (d : ℕ) :
    alphaMixCoeff μ
        (⨆ s ∈ Set.Iic k, MeasurableSpace.comap (X s) inferInstance ⊔
          MeasurableSpace.comap (e s) inferInstance)
        (⨆ s ∈ Set.Ici (k + (d : ℤ)), MeasurableSpace.comap (X s) inferInstance ⊔
          MeasurableSpace.comap (e s) inferInstance)
      = pairAlphaCoeff X e μ d := by
  have hZm : ∀ t : ℤ, Measurable (fun ω => pairCode (X t ω, e t ω)) := fun t =>
    pairCode.measurable.comp ((hmeasX t).prodMk (hmeasE t))
  have hLE : ∀ c : ℤ, sigmaLE (fun t ω => pairCode (X t ω, e t ω)) c
      = ⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance := fun c =>
    iSup_congr fun s => iSup_congr fun _ => comap_pairCode s
  have hGE : ∀ c : ℤ, sigmaGE (fun t ω => pairCode (X t ω, e t ω)) c
      = ⨆ s ∈ Set.Ici c, MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance := fun c =>
    iSup_congr fun s => iSup_congr fun _ => comap_pairCode s
  have hsh := (isStrictlyStationary_pairCode hmeasX hmeasE hstat).alphaMixCoeff_shift hZm k d
  rw [hLE k, hGE (k + (d : ℤ))] at hsh
  rw [hsh]
  show alphaMixCoeff μ (sigmaLE (fun t ω => pairCode (X t ω, e t ω)) 0)
      (sigmaGE (fun t ω => pairCode (X t ω, e t ω)) (d : ℤ)) = _
  rw [hLE 0, hGE (d : ℤ)]
  rfl

end Shift

end StatLean.TimeSeries
