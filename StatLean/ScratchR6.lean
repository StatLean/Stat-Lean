import StatLean.TimeSeries.Mixing.KernelRegressionCLT

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal NNReal

namespace ScratchR6

open StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- one-time law transport -/
theorem map_pair_eq_of_stat {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) :
    μ.map (fun ω => (X t ω, e t ω)) = μ.map (fun ω => (X 0 ω, e 0 ω)) := by
  have hmΦ : ∀ s : ℤ, Measurable (fun ω (i : Fin 1) => (X (s + (i : ℕ)) ω, e (s + (i : ℕ)) ω)) :=
    fun s => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hmΨ : Measurable (fun ω (i : Fin 1) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)) :=
    measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hev : Measurable (fun z : Fin 1 → ℝ × ℝ => z 0) := measurable_pi_apply 0
  have h := congrArg (fun ν : Measure (Fin 1 → ℝ × ℝ) => ν.map (fun z => z 0)) (hstat 1 t)
  simp only at h
  rw [Measure.map_map hev (hmΦ t), Measure.map_map hev hmΨ] at h
  simpa [Function.comp] using h

/-- two-time law transport -/
theorem map_pair2_eq_of_stat {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) (d : ℕ) :
    μ.map (fun ω => ((X t ω, e t ω), (X (t + (d : ℤ)) ω, e (t + (d : ℤ)) ω)))
      = μ.map (fun ω => ((X 0 ω, e 0 ω), (X (d : ℤ) ω, e (d : ℤ) ω))) := by
  have hmΦ : ∀ s : ℤ,
      Measurable (fun ω (i : Fin (d + 1)) => (X (s + (i : ℕ)) ω, e (s + (i : ℕ)) ω)) :=
    fun s => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hmΨ : Measurable (fun ω (i : Fin (d + 1)) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)) :=
    measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hev : Measurable
      (fun z : Fin (d + 1) → ℝ × ℝ => (z 0, z (Fin.last d))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have h := congrArg
    (fun ν : Measure (Fin (d + 1) → ℝ × ℝ) => ν.map (fun z => (z 0, z (Fin.last d))))
    (hstat (d + 1) t)
  simp only at h
  rw [Measure.map_map hev (hmΦ t), Measure.map_map hev hmΨ] at h
  simpa [Function.comp_def, Fin.val_last] using h

section Toolkit

variable {X e : ℤ → Ω → ℝ}

theorem integral_comp_pair_eq
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) :
    ∫ ω, F (X t ω, e t ω) ∂μ = ∫ ω, F (X 0 ω, e 0 ω) ∂μ := by
  have hmt : AEMeasurable (fun ω => (X t ω, e t ω)) μ :=
    ((hmeasX t).prodMk (hmeasE t)).aemeasurable
  have hm0 : AEMeasurable (fun ω => (X 0 ω, e 0 ω)) μ :=
    ((hmeasX 0).prodMk (hmeasE 0)).aemeasurable
  rw [← integral_map hmt hF.aestronglyMeasurable,
    map_pair_eq_of_stat hmeasX hmeasE hstat t, integral_map hm0 hF.aestronglyMeasurable]

theorem integral_comp_pair2_eq
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) (d : ℕ) {G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hG : Measurable G) :
    ∫ ω, G ((X t ω, e t ω), (X (t + (d : ℤ)) ω, e (t + (d : ℤ)) ω)) ∂μ
      = ∫ ω, G ((X 0 ω, e 0 ω), (X (d : ℤ) ω, e (d : ℤ) ω)) ∂μ := by
  have hmt : AEMeasurable
      (fun ω => ((X t ω, e t ω), (X (t + (d : ℤ)) ω, e (t + (d : ℤ)) ω))) μ :=
    (((hmeasX t).prodMk (hmeasE t)).prodMk
      ((hmeasX _).prodMk (hmeasE _))).aemeasurable
  have hm0 : AEMeasurable
      (fun ω => ((X 0 ω, e 0 ω), (X (d : ℤ) ω, e (d : ℤ) ω))) μ :=
    (((hmeasX 0).prodMk (hmeasE 0)).prodMk
      ((hmeasX _).prodMk (hmeasE _))).aemeasurable
  rw [← integral_map hmt hG.aestronglyMeasurable,
    map_pair2_eq_of_stat hmeasX hmeasE hstat t d, integral_map hm0 hG.aestronglyMeasurable]

theorem eLpNorm_comp_pair_eq
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) (q : ℝ≥0∞) :
    eLpNorm (fun ω => F (X t ω, e t ω)) q μ
      = eLpNorm (fun ω => F (X 0 ω, e 0 ω)) q μ := by
  have hmt : AEMeasurable (fun ω => (X t ω, e t ω)) μ :=
    ((hmeasX t).prodMk (hmeasE t)).aemeasurable
  have hm0 : AEMeasurable (fun ω => (X 0 ω, e 0 ω)) μ :=
    ((hmeasX 0).prodMk (hmeasE 0)).aemeasurable
  have h1 : eLpNorm F q (μ.map (fun ω => (X t ω, e t ω)))
      = eLpNorm (fun ω => F (X t ω, e t ω)) q μ :=
    eLpNorm_map_measure hF.aestronglyMeasurable hmt
  have h2 : eLpNorm F q (μ.map (fun ω => (X 0 ω, e 0 ω)))
      = eLpNorm (fun ω => F (X 0 ω, e 0 ω)) q μ :=
    eLpNorm_map_measure hF.aestronglyMeasurable hm0
  rw [← h1, ← h2, map_pair_eq_of_stat hmeasX hmeasE hstat t]

theorem memLp_comp_pair
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) {q : ℝ≥0∞}
    (h0 : MemLp (fun ω => F (X 0 ω, e 0 ω)) q μ) :
    MemLp (fun ω => F (X t ω, e t ω)) q μ :=
  ⟨(hF.comp ((hmeasX t).prodMk (hmeasE t))).aestronglyMeasurable, by
    rw [eLpNorm_comp_pair_eq hmeasX hmeasE hstat t hF q]; exact h0.2⟩

end Toolkit

section Combinatorics

theorem abs_double_sum_sub_diag_le (n : ℕ) (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hc : ∀ s d : ℕ, c s (s + d) = g d) (hc' : ∀ s d : ℕ, c (s + d) s = g d) :
    |(∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, c s t) - n * g 0|
      ≤ 2 * n * ∑ j ∈ Finset.Ico 1 n, |g j| := by
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 n, |g j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hdiag : ∀ s : ℕ, c s s = g 0 := fun s => by simpa using hc s 0
  have key : ∀ s ∈ Finset.range n,
      |(∑ t ∈ Finset.range n, c s t) - g 0|
        ≤ 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by
    intro s hs
    simp only [Finset.mem_range] at hs
    have hsplit : (∑ t ∈ Finset.range n, c s t)
        = g 0 + ∑ t ∈ (Finset.range n).erase s, c s t := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hs), hdiag]
    rw [hsplit, add_sub_cancel_left]
    set A : Finset ℕ := (Finset.range n).filter (fun t => t < s) with hA
    set B : Finset ℕ := (Finset.range n).filter (fun t => s < t) with hB
    have hAB : (Finset.range n).erase s = A ∪ B := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, hA, hB,
        Finset.mem_filter]
      omega
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro t htA htB
      simp only [hA, hB, Finset.mem_filter] at htA htB
      omega
    calc |∑ t ∈ (Finset.range n).erase s, c s t|
        ≤ ∑ t ∈ (Finset.range n).erase s, |c s t| :=
          Finset.abs_sum_le_sum_abs _ _
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
              simp only [Finset.mem_image, hA, Finset.mem_filter, Finset.mem_range] at hj
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
            exact Finset.sum_le_sum_of_subset_of_nonneg himg
              fun j _ _ => abs_nonneg _
          · have hinj : ∀ t₁ ∈ B, ∀ t₂ ∈ B, t₁ - s = t₂ - s → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hB, Finset.mem_filter] at h₁ h₂
              omega
            have himg : B.image (fun t => t - s) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hB, Finset.mem_filter, Finset.mem_range] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
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
            exact Finset.sum_le_sum_of_subset_of_nonneg himg
              fun j _ _ => abs_nonneg _
      _ = 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by ring
  have hrw : (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, c s t) - n * g 0
      = ∑ s ∈ Finset.range n, ((∑ t ∈ Finset.range n, c s t) - g 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrw]
  calc |∑ s ∈ Finset.range n, ((∑ t ∈ Finset.range n, c s t) - g 0)|
      ≤ ∑ s ∈ Finset.range n, |(∑ t ∈ Finset.range n, c s t) - g 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range n, 2 * ∑ j ∈ Finset.Ico 1 n, |g j| :=
        Finset.sum_le_sum key
    _ = 2 * n * ∑ j ∈ Finset.Ico 1 n, |g j| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Combinatorics

section Main

/-- stub for the private `smallLagCut` -/
noncomputable def smallLagCut (h : ℕ → ℝ) (n : ℕ) : ℕ := ⌈(h n * |Real.log (h n)|)⁻¹⌉₊

/-- stub of the file's proved (2.76) -/
theorem small_lag_covariance_bound {X e : ℤ → Ω → ℝ} {W : ℝ → ℝ} {x : ℝ}
    (hWm : Measurable W) {B : ℝ}
    (hC2 : ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {hn : ℝ} (hhn : 0 < hn) (j : ℤ) (hj : j ≠ 0) :
    |∫ ω, (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn)) ∂μ|
      ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) * ((∫ v, |W v|) * hn) ^ 2 := sorry

/-- stub of the file's proved (2.75) -/
theorem large_lag_covariance_bound [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {δ : ℝ} (hδ : 2 < δ) {W : ℝ → ℝ} {x : ℝ} (hWm : Measurable W)
    {hn : ℝ} (hhn : 0 < hn) (j : ℕ) (hj : 1 ≤ j)
    (hL0 : MemLp (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ)
    (hLj : MemLp (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn)) (ENNReal.ofReal δ) μ) :
    |cov[fun ω => e 0 ω * W ((X 0 ω - x) / hn),
        fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn); μ]|
      ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ)
        * (eLpNorm (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ).toReal
        * (eLpNorm (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn))
            (ENNReal.ofReal δ) μ).toReal := sorry

/-- stub of the file's proved repaired diagonal -/
theorem tendsto_localized_second_moment_debt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0)) {σsq p : ℝ → ℝ}
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {x : ℝ}
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (he2 : Integrable (fun ω => e 0 ω ^ 2) μ)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x)
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := sorry


section DeltaMoment

-- the tower/density/change-of-variables chain below is elaboration-heavy
set_option maxHeartbeats 400000 in
/-- FY's implicit (2.74): the conditional δ-th moment bound, together with a bounded
density, gives `E|ξ_0|^δ = O(h)` for the kernel-localized summand. -/
theorem localized_delta_moment_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0))
    {p : ℝ → ℝ} (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {δ : ℝ} (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    {M : ℝ}
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {x hn : ℝ} (hhn : 0 < hn) :
    ∫ ω, |e 0 ω * W ((X 0 ω - x) / hn)| ^ δ ∂μ
      ≤ (M * Cp * ∫ v, |W v| ^ δ) * hn := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) :=
    (Real.continuous_rpow_const hδ0.le).measurable
  have hWam : Measurable (fun v => |W v| ^ δ) := hrp.comp hWm.abs
  have hGm : Measurable (fun v => |W ((v - x) / hn)| ^ δ) :=
    hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
  -- `|W|^δ` is integrable: `|W|^δ ≤ CW^{δ-2} W²`
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
  have hG0 : ∀ v : ℝ, 0 ≤ |W ((v - x) / hn)| ^ δ := fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hGb : ∀ v : ℝ, |(|W ((v - x) / hn)| ^ δ)| ≤ CW ^ δ := by
    intro v
    rw [abs_of_nonneg (hG0 v)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le
  -- `|e_0|^δ` is integrable
  have hζ : Integrable (fun ω => |e 0 ω| ^ δ) μ := by
    have hr := heLδ.integrable_norm_rpow (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0) ENNReal.ofReal_ne_top
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ0.le] using hr
  have hZ0 : (0 : Ω → ℝ)
      ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
    condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  have hM0 : (0 : ℝ) ≤ M := by
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  have hGXm : Measurable (fun ω => |W ((X 0 ω - x) / hn)| ^ δ) := hGm.comp hX
  -- tower: replace `|e_0|^δ` by its conditional expectation, then bound by `M`
  have htow : ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * |e 0 ω| ^ δ ∂μ
      = ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) *
          (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ :=
    integral_bdd_comp_mul_eq_of_condExp hX hζ (Filter.EventuallyEq.refl _ _)
      (fun v => |W ((v - x) / hn)| ^ δ) hGm hGb
  have hmono : ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ
      ≤ ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * M ∂μ := by
    refine integral_mono_ae
      (integrable_condExp.bdd_mul hGXm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _))
      ((integrable_const M).bdd_mul hGXm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _)) ?_
    filter_upwards [heδc] with ω hω
    exact mul_le_mul_of_nonneg_left hω (hG0 _)
  -- density substitution and the affine change of variables
  have hdens : ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * M ∂μ
      = M * ∫ v, p v * |W ((v - x) / hn)| ^ δ := by
    have hsub : ∫ ω, (fun v => |W ((v - x) / hn)| ^ δ * M) (X 0 ω) ∂μ
        = ∫ v, p v * (|W ((v - x) / hn)| ^ δ * M) :=
      integral_comp_eq_integral_density hX hmp hp0 hpd
        (fun v => |W ((v - x) / hn)| ^ δ * M) (hGm.mul_const M)
    have hpull : ∫ v, p v * (|W ((v - x) / hn)| ^ δ * M)
        = M * ∫ v, p v * |W ((v - x) / hn)| ^ δ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun v => by ring)
    rw [← hpull, ← hsub]
  have hcov : ∫ u, |W u| ^ δ * p (x + hn * u) = hn⁻¹ * ∫ v, |W ((v - x) / hn)| ^ δ * p v :=
    integral_dilate_translate (fun u => |W u| ^ δ) p x hhn
  have hpint : ∫ v, p v * |W ((v - x) / hn)| ^ δ
      = hn * ∫ u, |W u| ^ δ * p (x + hn * u) := by
    rw [hcov, ← mul_assoc, mul_inv_cancel₀ hhn.ne', one_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  have hlast : ∫ u, |W u| ^ δ * p (x + hn * u) ≤ Cp * ∫ u, |W u| ^ δ := by
    have hi : Integrable (fun u => |W u| ^ δ * p (x + hn * u)) MeasureTheory.volume := by
      refine Integrable.mono (hWδ.const_mul Cp)
        (hWam.mul (hmp.comp (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hp0 _)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Cp * |W u| ^ δ), mul_comm Cp]
      exact mul_le_mul_of_nonneg_left (hpb _) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [← integral_const_mul]
    refine integral_mono hi (hWδ.const_mul Cp) fun u => ?_
    rw [mul_comm Cp]
    exact mul_le_mul_of_nonneg_left (hpb _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hstart : ∫ ω, |e 0 ω * W ((X 0 ω - x) / hn)| ^ δ ∂μ
      = ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * |e 0 ω| ^ δ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change |e 0 ω * W ((X 0 ω - x) / hn)| ^ δ = |W ((X 0 ω - x) / hn)| ^ δ * |e 0 ω| ^ δ
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm]
  rw [hstart, htow]
  calc ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ
      ≤ ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * M ∂μ := hmono
    _ = M * ∫ v, p v * |W ((v - x) / hn)| ^ δ := hdens
    _ = M * (hn * ∫ u, |W u| ^ δ * p (x + hn * u)) := by rw [hpint]
    _ ≤ M * (hn * (Cp * ∫ u, |W u| ^ δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hhn.le) hM0
    _ = (M * Cp * ∫ v, |W v| ^ δ) * hn := by ring

end DeltaMoment

section Limits

/-- `h_n → 0⁺` in the punctured-right sense. -/
theorem tendsto_nhdsGT_of_pos {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) : Tendsto h atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h hh
    (Eventually.of_forall fun n => hh0 n)

/-- `|log h_n| → ∞`. -/
theorem tendsto_abs_log_atTop {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => |Real.log (h n)|) atTop atTop :=
  tendsto_abs_atBot_atTop.comp
    (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsGT_of_pos hh0 hh))

/-- FY's `m_n h_n → 0`: the small-lag cut costs only `1/|log h|`. -/
theorem tendsto_smallLagCut_mul_bandwidth {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => (smallLagCut h n : ℝ) * h n) atTop (𝓝 0) := by
  have hL := tendsto_abs_log_atTop hh0 hh
  have hLinv : Tendsto (fun n => |Real.log (h n)|⁻¹) atTop (𝓝 0) := hL.inv_tendsto_atTop
  refine squeeze_zero' (Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg _) (hh0 n).le) ?_
    (by simpa using hLinv.add hh)
  filter_upwards [hL.eventually_gt_atTop 0] with n hLn
  have hhn := hh0 n
  have hx : (0 : ℝ) ≤ (h n * |Real.log (h n)|)⁻¹ := by positivity
  have hceil : ((smallLagCut h n : ℕ) : ℝ) < (h n * |Real.log (h n)|)⁻¹ + 1 :=
    Nat.ceil_lt_add_one hx
  have hstep : ((smallLagCut h n : ℕ) : ℝ) * h n
      ≤ ((h n * |Real.log (h n)|)⁻¹ + 1) * h n :=
    mul_le_mul_of_nonneg_right hceil.le hhn.le
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- `h^a |log h|^λ → 0` for `a, λ > 0`. -/
theorem tendsto_rpow_mul_abs_log_rpow {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) {a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun n => h n ^ a * |Real.log (h n)| ^ lam) atTop (𝓝 0) := by
  -- the base sequence `h^{a/λ} |log h| → 0`
  have hφ : Tendsto (fun y : ℝ => y ^ (a / lam) * |Real.log y|) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.log y * y ^ (a / lam)) (𝓝[>] 0) (𝓝 0) :=
      _root_.tendsto_log_mul_rpow_nhdsGT_zero (by positivity)
    have h2 : Tendsto (fun y : ℝ => |Real.log y * y ^ (a / lam)|) (𝓝[>] 0) (𝓝 0) := by
      simpa using h1.abs
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hy0.le _), mul_comm]
  have hbase : Tendsto (fun n => h n ^ (a / lam) * |Real.log (h n)|) atTop (𝓝 0) :=
    hφ.comp (tendsto_nhdsGT_of_pos hh0 hh)
  -- raise to the power `λ`
  have hcont : Tendsto (fun y : ℝ => y ^ lam) (𝓝 0) (𝓝 0) := by
    have hz : (0 : ℝ) ^ lam = 0 := Real.zero_rpow hlam.ne'
    have ht := (Real.continuousAt_rpow_const (0 : ℝ) lam (Or.inr hlam.le)).tendsto
    rw [hz] at ht
    exact ht
  have hcomp := hcont.comp hbase
  refine hcomp.congr fun n => ?_
  have hhn := hh0 n
  simp only [Function.comp_apply]
  rw [Real.mul_rpow (Real.rpow_nonneg hhn.le _) (abs_nonneg _), ← Real.rpow_mul hhn.le,
    div_mul_cancel₀ _ hlam.ne']

end Limits

theorem var_localized_sum' [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g →
      (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    (hKh : ∃ K : ℝ, ∀ n : ℕ,
      ∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ ≤ K * h n) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ Finset.range n,
          e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      atTop (𝓝 (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume)) := by
  obtain ⟨B, hB0, hB⟩ := hC2
  obtain ⟨K, hK⟩ := hKh
  -- numerology
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hδ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hδ2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have he1 : Integrable (e 0) μ := heLδ.integrable hδ1
  have he2 : Integrable (fun ω => e 0 ω ^ 2) μ := (heLδ.mono_exponent hδ2).integrable_sq
  -- the localized summand, as a function of the pair `(X_t, e_t)`
  have hFm : ∀ hn : ℝ, Measurable (fun z : ℝ × ℝ => z.2 * W ((z.1 - x) / hn)) := by
    intro hn; fun_prop
  -- localized summands: measurability, L^δ and L²
  have hmξ : ∀ (hn : ℝ) (t : ℤ), Measurable (fun ω => e t ω * W ((X t ω - x) / hn)) := fun hn t =>
    (hmeasE t).mul (hWm.comp (((hmeasX t).sub measurable_const).div measurable_const))
  have hLδ0 : ∀ hn : ℝ, MemLp (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ := by
    intro hn
    refine MemLp.of_le (heLδ.const_mul CW) (hmξ hn 0).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hCW0]
    nlinarith [hWb ((X 0 ω - x) / hn), abs_nonneg (e 0 ω), abs_nonneg (W ((X 0 ω - x) / hn))]
  have hLδt : ∀ (hn : ℝ) (t : ℤ),
      MemLp (fun ω => e t ω * W ((X t ω - x) / hn)) (ENNReal.ofReal δ) μ := fun hn t =>
    memLp_comp_pair hmeasX hmeasE hstat t (hFm hn) (hLδ0 hn)
  have hL2t : ∀ (hn : ℝ) (t : ℤ), MemLp (fun ω => e t ω * W ((X t ω - x) / hn)) 2 μ :=
    fun hn t => (hLδt hn t).mono_exponent hδ2
  have hint : ∀ (hn : ℝ) (s t : ℤ), Integrable (fun ω =>
      (e s ω * W ((X s ω - x) / hn)) * (e t ω * W ((X t ω - x) / hn))) μ := fun hn s t =>
    (hL2t hn s).integrable_mul (hL2t hn t)
  -- each localized summand is centred
  have hmean0 : ∀ hn : ℝ, ∫ ω, e 0 ω * W ((X 0 ω - x) / hn) ∂μ = 0 := by
    intro hn
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX 0) he1 hce
      (fun v => W ((v - x) / hn)) (by fun_prop) (C := CW) (fun v => hWb _)
    calc ∫ ω, e 0 ω * W ((X 0 ω - x) / hn) ∂μ
        = ∫ ω, W ((X 0 ω - x) / hn) * e 0 ω ∂μ :=
          integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      _ = ∫ ω, W ((X 0 ω - x) / hn) * (0 : Ω → ℝ) ω ∂μ := hz
      _ = 0 := by simp
  -- lag covariances and the pair covariance array
  set Gl : ℕ → ℕ → ℝ := fun n j =>
    ∫ ω, (e 0 ω * W ((X 0 ω - x) / h n)) *
      (e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / h n)) ∂μ with hGldef
  set Cl : ℕ → ℕ → ℕ → ℝ := fun n s t =>
    ∫ ω, (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
      (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ∂μ with hCldef
  have hCG : ∀ n s d : ℕ, Cl n s (s + d) = Gl n d := by
    intro n s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr : ∫ ω, (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
          (e (((s : ℤ) + 1) + (d : ℤ)) ω *
            W ((X (((s : ℤ) + 1) + (d : ℤ)) ω - x) / h n)) ∂μ
        = ∫ ω, (e 0 ω * W ((X 0 ω - x) / h n)) *
          (e ((d : ℕ) : ℤ) ω * W ((X ((d : ℕ) : ℤ) ω - x) / h n)) ∂μ :=
      integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
        (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          (z.1.2 * W ((z.1.1 - x) / h n)) * (z.2.2 * W ((z.2.1 - x) / h n)))
        (by fun_prop)
    simp only [hCldef, hGldef, hidx]
    exact htr
  have hCG' : ∀ n s d : ℕ, Cl n (s + d) s = Gl n d := by
    intro n s d
    have hsym : Cl n (s + d) s = Cl n s (s + d) := by
      simp only [hCldef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  have hG0 : ∀ n : ℕ, Gl n 0 = ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
    intro n
    simp only [hGldef, Nat.cast_zero]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  -- the square of the localized sum expands into the covariance array
  have hexp : ∀ n : ℕ, ∫ ω, (∑ t ∈ Finset.range n,
        e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
      = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cl n s t := by
    intro n
    have hsq : ∀ ω : Ω, (∑ t ∈ Finset.range n,
          e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2
        = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
            (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
              (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) := by
      intro ω
      rw [sq, Finset.sum_mul_sum]
    simp only [hsq, hCldef]
    have h1 : ∫ ω, (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
          (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
            (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))) ∂μ
        = ∑ s ∈ Finset.range n, ∫ ω, (∑ t ∈ Finset.range n,
            (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
              (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))) ∂μ :=
      integral_finset_sum _ (fun s _ =>
        integrable_finset_sum _ (fun t _ => hint (h n) ((s : ℤ) + 1) ((t : ℤ) + 1)))
    rw [h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact integral_finset_sum _ (fun t _ => hint (h n) ((s : ℤ) + 1) ((t : ℤ) + 1))
  -- the δ-th moment input (2.74), in eLpNorm form, at every time
  have hK0 : (0 : ℝ) ≤ K := by
    have h1 : (0 : ℝ) ≤ ∫ ω, |e 0 ω * W ((X 0 ω - x) / h 0)| ^ δ ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
    have h2 := hK 0
    have h3 := hh0 0
    nlinarith
  have hnormδ : ∀ (n : ℕ) (t : ℤ),
      (eLpNorm (fun ω => e t ω * W ((X t ω - x) / h n)) (ENNReal.ofReal δ) μ).toReal
        ≤ (K * h n) ^ (1 / δ) := by
    intro n t
    have hEq : eLpNorm (fun ω => e t ω * W ((X t ω - x) / h n)) (ENNReal.ofReal δ) μ
        = eLpNorm (fun ω => e 0 ω * W ((X 0 ω - x) / h n)) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t (hFm (h n)) _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := (hLδ0 (h n)).eLpNorm_eq_integral_rpow_norm hp1 ENNReal.ofReal_ne_top
    have hbase : (0 : ℝ) ≤ ∫ a, ‖e 0 a * W ((X 0 a - x) / h n)‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hbase _), ← one_div]
    have hnn : ∫ a, ‖e 0 a * W ((X 0 a - x) / h n)‖ ^ δ ∂μ ≤ K * h n := by
      simpa only [Real.norm_eq_abs] using hK n
    exact Real.rpow_le_rpow hbase hnn (by positivity)
  -- (2.76): the small-lag bound
  have hsmall : ∀ (n j : ℕ), 1 ≤ j →
      |Gl n j| ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) * ((∫ v, |W v|) * h n) ^ 2 := by
    intro n j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    simp only [hGldef]
    exact small_lag_covariance_bound hWm hB (hh0 n) (j : ℤ) hjz
  -- (2.75): the large-lag bound, with the localized δ-norms
  have hlarge : ∀ (n j : ℕ), 1 ≤ j →
      |Gl n j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (K * h n) ^ (2 / δ) := by
    intro n j hj
    have hcov : cov[fun ω => e 0 ω * W ((X 0 ω - x) / h n),
        fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / h n); μ] = Gl n j := by
      rw [covariance_eq_sub (hL2t (h n) 0) (hL2t (h n) (j : ℤ)), hmean0 (h n), zero_mul,
        sub_zero]
      simp only [hGldef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound hmeasX hmeasE hδ hWm (hh0 n) j hj
      (hLδ0 (h n)) (hLδt (h n) (j : ℤ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ K * h n := mul_nonneg hK0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (K * h n) ^ (2 / δ) = (K * h n) ^ (1 / δ) * (K * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδ n 0
    · exact hnormδ n (j : ℤ)
  -- constants
  set E2 : ℝ := ∫ ω, e 0 ω ^ 2 ∂μ with hE2def
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hE20 : (0 : ℝ) ≤ E2 := integral_nonneg fun ω => sq_nonneg _
  have hIW0 : (0 : ℝ) ≤ IW := integral_nonneg fun v => abs_nonneg _
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  -- FY's split of the lag sum at `m_n`
  have hsplit : ∀ n : ℕ, 1 ≤ smallLagCut h n →
      ∑ j ∈ Finset.Ico 1 n, |Gl n j|
        ≤ (smallLagCut h n : ℝ) * (B * E2 * (IW * h n) ^ 2)
          + 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    intro n hm1
    have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gl n j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gl n j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gl n j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gl n j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gl n j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gl n j|
        ≤ (smallLagCut h n : ℝ) * (B * E2 * (IW * h n) ^ 2) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gl n j|) (B * E2 * (IW * h n) ^ 2)
        (fun j hj => hsmall n j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gl n j|
        ≤ 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (K * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hK0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gl n j| ≤ 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
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
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (K * h n) ^ (2 / δ)
            = 8 * (K * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (K * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by
              gcongr
          _ = 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  -- the two sequences of FY's decomposition
  set A : ℕ → ℝ := fun n => ((n : ℝ) * h n)⁻¹ *
    ∫ ω, (∑ t ∈ Finset.range n,
      e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ with hAdef
  set Dg : ℕ → ℝ := fun n =>
    (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ with hDdef
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |A n - Dg n| ≤ 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gl n j| := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hhn : 0 < h n := hh0 n
    have hAn : A n = ((n : ℝ) * h n)⁻¹ *
        (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cl n s t) := by
      simp only [hAdef]; rw [hexp n]
    have hDn : Dg n = ((n : ℝ) * h n)⁻¹ * ((n : ℝ) * Gl n 0) := by
      simp only [hDdef]; rw [← hG0 n]; field_simp
    rw [hAn, hDn, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h n)⁻¹)]
    calc ((n : ℝ) * h n)⁻¹ *
          |(∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cl n s t) - (n : ℝ) * Gl n 0|
        ≤ ((n : ℝ) * h n)⁻¹ * (2 * (n : ℝ) * ∑ j ∈ Finset.Ico 1 n, |Gl n j|) :=
          mul_le_mul_of_nonneg_left
            (abs_double_sum_sub_diag_le n (Cl n) (Gl n) (hCG n) (hCG' n)) (by positivity)
      _ = 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gl n j| := by field_simp
  -- the lag remainder vanishes
  have hRto0 : Tendsto (fun n : ℕ => 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gl n j|)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (2 * B * E2 * IW ^ 2) * ((smallLagCut h n : ℝ) * h n)
          + (16 * SA * K ^ (2 / δ)) *
            (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam)) atTop (𝓝 0) := by
      have t1 := (tendsto_smallLagCut_mul_bandwidth hh0 hh).const_mul (2 * B * E2 * IW ^ 2)
      have t2 := (tendsto_rpow_mul_abs_log_rpow hh0 hh (a := 2 / δ - 1 + lam)
        (by linarith) hlam0).const_mul (16 * SA * K ^ (2 / δ))
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
      have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) * (B * E2 * (IW * h n) ^ 2))
          = (2 * B * E2 * IW ^ 2) * ((smallLagCut h n : ℝ) * h n) := by
        field_simp
      have hKrw : (K * h n) ^ (2 / δ) = K ^ (2 / δ) * (h n) ^ (2 / δ) :=
        Real.mul_rpow hK0 hhn.le
      have hLrw : (h n * |Real.log (h n)|) ^ lam
          = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
      have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
        rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
          Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
      have hKh : (0 : ℝ) ≤ (K * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hK0 hhn.le) _
      have e2 : 2 * (h n)⁻¹ * (8 * (K * h n) ^ (2 / δ) *
            ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ (16 * SA * K ^ (2 / δ)) *
            ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
        calc 2 * (h n)⁻¹ *
              (8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
            ≤ 2 * (h n)⁻¹ * (8 * (K * h n) ^ (2 / δ) *
                ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
          _ = (16 * SA * K ^ (2 / δ)) *
                ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
              rw [hKrw, hLrw, hpow]; ring
      linarith
  -- assemble
  have hDlim : Tendsto Dg atTop (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) :=
    tendsto_localized_second_moment_debt (hmeasX 0) hσm hmp hp0 hpd hcv he2 hσc hpc hσpb
      hWm hWb hW2 hh0 hh
  have hdiff : Tendsto (fun n => A n - Dg n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hRto0
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs] using hbound n hn
  simpa using hdiff.add hDlim

end Main

end ScratchR6
