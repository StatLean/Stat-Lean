import StatLean.TimeSeries.Mixing.KernelRegressionCLT

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Pointwise truncation residual, linear form. -/
theorem abs_sub_clamp_le {δ L z : ℝ} (hδ : 2 < δ) (hL : 0 < L) :
    |z - clampAt L z| ≤ L ^ (1 - δ) * |z| ^ δ := by
  rcases le_or_gt |z| L with hz | hz
  · have h1 : min L z = z := min_eq_right (le_trans (le_abs_self z) hz)
    have h2 : max (-L) z = z := max_eq_right (by have := neg_abs_le z; linarith)
    have hz0 : z - clampAt L z = 0 := by simp [clampAt, h1, h2]
    rw [hz0, abs_zero]
    positivity
  · have hzpos : (0 : ℝ) < |z| := lt_trans hL hz
    have habs : |z - clampAt L z| ≤ |z| := by
      rcases le_or_gt z 0 with hz0 | hz0
      · have hzneg : z < -L := by rw [abs_of_nonpos hz0] at hz; linarith
        have h1 : min L z = z := min_eq_right (by linarith)
        have h2 : max (-L) z = -L := max_eq_left (by linarith)
        simp only [clampAt, h1, h2]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
        linarith
      · have hzpos' : L < z := by rw [abs_of_pos hz0] at hz; exact hz
        have h1 : min L z = L := min_eq_left (by linarith)
        have h2 : max (-L) L = L := max_eq_right (by linarith)
        simp only [clampAt, h1, h2]
        rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
        linarith
    refine habs.trans ?_
    have h1 : L ^ (δ - 1) ≤ |z| ^ (δ - 1) := Real.rpow_le_rpow hL.le hz.le (by linarith)
    have hsplit : |z| ^ (δ - 1) * |z| = |z| ^ δ := by
      nth_rewrite 2 [← Real.rpow_one |z|]
      rw [← Real.rpow_add hzpos]
      ring_nf
    have hone : L ^ (1 - δ) * L ^ (δ - 1) = 1 := by
      rw [← Real.rpow_add hL]; norm_num
    calc |z| = (L ^ (1 - δ) * L ^ (δ - 1)) * |z| := by rw [hone, one_mul]
      _ ≤ (L ^ (1 - δ) * |z| ^ (δ - 1)) * |z| := by gcongr
      _ = L ^ (1 - δ) * (|z| ^ (δ - 1) * |z|) := by ring
      _ = L ^ (1 - δ) * |z| ^ δ := by rw [hsplit]

/-- The recentring constant of `truncErr` decays in `L`. -/
theorem exists_truncErr_repr_decay [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {δ M : ℝ} (hδ : 2 < δ) (he1 : Integrable (e 0) μ)
    (heδi : Integrable (fun ω => |e 0 ω| ^ δ) μ)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    {L : ℝ} (hL : 0 < L) :
    ∃ mL : ℝ → ℝ, Measurable mL ∧ (∀ v, |mL v| ≤ M * L ^ (1 - δ)) ∧
      ∀ t : ℤ, truncErr X e μ L t =ᵐ[μ] fun ω => clampAt L (e t ω) - mL (X t ω) := by
  classical
  obtain ⟨m, hm, hmB, hrep⟩ := exists_truncErr_repr hmeasX hmeasE hstat hL
  have hM0 : (0 : ℝ) ≤ M := by
    have hZ0 : (0 : Ω → ℝ)
        ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
      condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  set c : ℝ := M * L ^ (1 - δ) with hcdef
  have hc0 : (0 : ℝ) ≤ c := mul_nonneg hM0 (Real.rpow_nonneg hL.le _)
  have hcli : Integrable (fun ω => clampAt L (e 0 ω)) μ := by
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE 0)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL.le _
  have hdiffi : Integrable (fun ω => clampAt L (e 0 ω) - e 0 ω) μ := hcli.sub he1
  -- the conditional expectation of the residual is `m (X 0 ·)`
  have hsub : μ[fun ω => clampAt L (e 0 ω) - e 0 ω | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω =>
        (μ[fun ω' => clampAt L (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]) ω
          - (μ[e 0 | MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_sub hcli he1 _
  have hkey : ∀ᵐ ω ∂μ,
      (μ[fun ω' => clampAt L (e 0 ω') - e 0 ω' |
        MeasurableSpace.comap (X 0) inferInstance]) ω = m (X 0 ω) := by
    filter_upwards [hsub, hrep 0, hce] with ω ha hb hc
    simp only [truncErr] at hb
    have hb' : (μ[fun ω' => clampAt L (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]) ω
        = m (X 0 ω) := by linarith
    have hc' : (μ[e 0 | MeasurableSpace.comap (X 0) inferInstance]) ω = 0 := hc
    rw [ha, hb', hc', sub_zero]
  -- and it is bounded by `c` in absolute value
  have hup := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hdiffi
    (heδi.const_mul (L ^ (1 - δ)))
    (Eventually.of_forall fun ω => le_trans (le_abs_self _) (by
      rw [abs_sub_comm]; exact abs_sub_clamp_le hδ hL))
  have hlo := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
    ((heδi.const_mul (L ^ (1 - δ))).neg) hdiffi
    (Eventually.of_forall fun ω => by
      have h2 : |clampAt L (e 0 ω) - e 0 ω| ≤ L ^ (1 - δ) * |e 0 ω| ^ δ := by
        rw [abs_sub_comm]; exact abs_sub_clamp_le hδ hL
      have h3 := neg_abs_le (clampAt L (e 0 ω) - e 0 ω)
      simp only [Pi.neg_apply]
      linarith)
  have hnegE : μ[-fun ω => L ^ (1 - δ) * |e 0 ω| ^ δ |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] -μ[fun ω => L ^ (1 - δ) * |e 0 ω| ^ δ |
        MeasurableSpace.comap (X 0) inferInstance] := condExp_neg _ _
  have hsm : μ[fun ω => L ^ (1 - δ) * |e 0 ω| ^ δ |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => L ^ (1 - δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_smul (𝕜 := ℝ) (L ^ (1 - δ)) (fun ω => |e 0 ω| ^ δ)
      (MeasurableSpace.comap (X 0) inferInstance)
  have hae : ∀ᵐ ω ∂μ, X 0 ω ∈ {v : ℝ | |m v| ≤ c} := by
    filter_upwards [hkey, hup, hlo, hnegE, hsm, heδc] with ω h0 h1 h2 h3 h4 h5
    show |m (X 0 ω)| ≤ c
    rw [← h0]
    have hMb : L ^ (1 - δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω
          ≤ M * L ^ (1 - δ) := by
      have := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hL.le (1 - δ))
      calc L ^ (1 - δ) *
            (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω
          ≤ L ^ (1 - δ) * M := this
        _ = M * L ^ (1 - δ) := by ring
    simp only [Pi.neg_apply] at h3
    rw [h4] at h1 h3
    rw [hcdef, abs_le]
    constructor
    · rw [h3] at h2; linarith
    · linarith
  have hS : MeasurableSet {v : ℝ | |m v| ≤ c} := measurableSet_le hm.abs measurable_const
  refine ⟨fun v => clampAt c (m v), (measurable_clampAt c).comp hm,
    fun v => abs_clampAt_le hc0 _, fun t => ?_⟩
  filter_upwards [hrep t, ae_comp_X_of_stat hmeasX hmeasE hstat t hS hae] with ω h1 h2
  have h2' : |m (X t ω)| ≤ c := h2
  have hcl : clampAt c (m (X t ω)) = m (X t ω) := by
    unfold clampAt
    rw [min_eq_right (abs_le.1 h2').2, max_eq_right (abs_le.1 h2').1]
  rw [h1, hcl]

/-- Charfun Lipschitz bound. -/
theorem norm_charFun_map_sub_le [IsProbabilityMeasure μ] {S T : Ω → ℝ}
    (hS : Measurable S) (hT : Measurable T)
    (hi : Integrable (fun ω => |S ω - T ω|) μ) (u : ℝ) :
    ‖charFun (μ.map S) u - charFun (μ.map T) u‖ ≤ |u| * ∫ ω, |S ω - T ω| ∂μ := by
  have hc : Continuous fun z : ℝ => Complex.exp ((u : ℂ) * (z : ℂ) * Complex.I) := by fun_prop
  have hbdd : ∀ (f : Ω → ℝ) (ω : Ω),
      ‖Complex.exp ((u : ℂ) * (f ω : ℂ) * Complex.I)‖ = 1 := by
    intro f ω
    rw [show ((u : ℂ) * (f ω : ℂ) * Complex.I) = ((u * f ω : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ f : Ω → ℝ, Measurable f →
      Integrable (fun ω => Complex.exp ((u : ℂ) * (f ω : ℂ) * Complex.I)) μ := by
    intro f hf
    exact (integrable_const (1 : ℝ)).mono' (hc.measurable.comp hf).aestronglyMeasurable
      (Eventually.of_forall fun ω => le_of_eq (hbdd f ω))
  have hmapS : charFun (μ.map S) u
      = ∫ ω, Complex.exp ((u : ℂ) * (S ω : ℂ) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hS.aemeasurable hc.aestronglyMeasurable]
  have hmapT : charFun (μ.map T) u
      = ∫ ω, Complex.exp ((u : ℂ) * (T ω : ℂ) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hT.aemeasurable hc.aestronglyMeasurable]
  rw [hmapS, hmapT, ← integral_sub (hint S hS) (hint T hT)]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((hint S hS).sub (hint T hT)).norm (hi.const_mul |u|) fun ω => ?_
  have hfac : Complex.exp ((u : ℂ) * (S ω : ℂ) * Complex.I)
        - Complex.exp ((u : ℂ) * (T ω : ℂ) * Complex.I)
      = Complex.exp ((u : ℂ) * (T ω : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((u * (S ω - T ω) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hfac, norm_mul, hbdd T ω, one_mul]
  refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
  rw [Real.norm_eq_abs, abs_mul]

set_option maxHeartbeats 4000000 in
/-- **Uniform-in-`n` L²-bound for the truncation residual.** -/
theorem residual_variance_bound [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {M Cp : ℝ}
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    (hpb : ∀ v, p v ≤ Cp)
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
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    ∃ C1 C2 C3 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ 0 ≤ C3 ∧ ∀ᶠ n : ℕ in atTop, ∀ L : ℝ, 1 ≤ L →
      ∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ
        ≤ (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)) * (1 + (smallLagCut h n : ℝ) * h n)
          + C3 * (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
  classical
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) := (Real.continuous_rpow_const hδ0.le).measurable
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
  -- moments of `e 0`
  have hδ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hδ2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have he1 : Integrable (e 0) μ := heLδ.integrable hδ1
  have heδi : Integrable (fun ω => |e 0 ω| ^ δ) μ := by
    have hr := heLδ.integrable_norm_rpow (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0) ENNReal.ofReal_ne_top
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ0.le] using hr
  have hM0 : (0 : ℝ) ≤ M := by
    have hZ0 : (0 : Ω → ℝ)
        ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
      condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  -- constants
  set IW2 : ℝ := ∫ v, W v ^ 2 with hIW2def
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set IWδ : ℝ := ∫ v, |W v| ^ δ with hIWδdef
  set Eδ : ℝ := ∫ ω, |e 0 ω| ^ δ ∂μ with hEδdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hIW20 : (0 : ℝ) ≤ IW2 := integral_nonneg fun v => sq_nonneg _
  have hIW0 : (0 : ℝ) ≤ IW := integral_nonneg fun v => abs_nonneg _
  have hIWδ0 : (0 : ℝ) ≤ IWδ := integral_nonneg fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hEδ0 : (0 : ℝ) ≤ Eδ := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  set Kρ : ℝ := (2 : ℝ) ^ δ * (M + M ^ δ) * (Cp * IWδ) with hKρdef
  have hKρ0 : (0 : ℝ) ≤ Kρ :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (by positivity)) (mul_nonneg hCp0 hIWδ0)
  refine ⟨2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ,
    2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2, 16 * SA * Kρ ^ (2 / δ),
    by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_abs_log_atTop hh0 hh).eventually_gt_atTop 0] with n hn1 hlogn
  intro L hL
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨mL, hmLm, hmLB, hmLrep⟩ :=
    exists_truncErr_repr_decay hmeasX hmeasE hstat hδ he1 heδi hce heδc hL0
  set c : ℝ := M * L ^ (1 - δ) with hcdef
  have hc0 : (0 : ℝ) ≤ c := mul_nonneg hM0 (Real.rpow_nonneg hL0.le _)
  have hcM : c ≤ M := by
    have h1 : L ^ (1 - δ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith : (1 : ℝ) - δ ≤ 0)
    rw [hcdef]
    nlinarith
  -- the residual array
  set q : ℝ → ℝ := fun y => |y - clampAt L y| + c with hqdef
  have hqm : Measurable q := ((measurable_id.sub (measurable_clampAt L)).abs).add_const c
  have hq0 : ∀ y, 0 ≤ q y := fun y => by positivity
  set Fr : ℝ × ℝ → ℝ := fun z => (z.2 - clampAt L z.2 + mL z.1) * W ((z.1 - x) / h n)
    with hFrdef
  have hFrm : Measurable Fr :=
    (((measurable_snd.sub ((measurable_clampAt L).comp measurable_snd)).add
      (hmLm.comp measurable_fst))).mul
      (hWm.comp ((measurable_fst.sub measurable_const).div measurable_const))
  have hFrb : ∀ z : ℝ × ℝ, |Fr z| ≤ q z.2 * |W ((z.1 - x) / h n)| := by
    intro z
    rw [hFrdef]
    simp only [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |z.2 - clampAt L z.2 + mL z.1| ≤ |z.2 - clampAt L z.2| + |mL z.1| := abs_add_le _ _
      _ ≤ |z.2 - clampAt L z.2| + c := by
          have := hmLB z.1
          rw [hcdef] at this ⊢
          linarith
  set R : ℤ → Ω → ℝ := fun t ω => Fr (X t ω, e t ω) with hRdef
  have hRm : ∀ t : ℤ, Measurable (R t) := fun t =>
    hFrm.comp ((hmeasX t).prodMk (hmeasE t))
  have hRrep : ∀ t : ℤ, (fun ω => e t ω * W ((X t ω - x) / h n)
      - truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] R t := by
    intro t
    filter_upwards [hmLrep t] with ω hω
    simp only [hRdef, hFrdef, hω]
    ring
  -- membership in `L^δ`
  have hMemq : MemLp (fun ω => CW * (‖e 0 ω‖ + c)) (ENNReal.ofReal δ) μ :=
    ((heLδ.norm).add (memLp_const c)).const_mul CW
  have hMemR0 : MemLp (R 0) (ENNReal.ofReal δ) μ := by
    refine MemLp.of_le hMemq (hRm 0).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs]
    have h1 := hFrb (X 0 ω, e 0 ω)
    have h2 : q (e 0 ω) ≤ |e 0 ω| + c := by
      rw [hqdef]
      simp only
      have := abs_sub_clamp_le (δ := δ) (L := L) (z := e 0 ω) hδ hL0
      have h3 : |e 0 ω - clampAt L (e 0 ω)| ≤ |e 0 ω| := by
        rcases le_or_gt |e 0 ω| L with hz | hz
        · have hmin : min L (e 0 ω) = e 0 ω :=
            min_eq_right (le_trans (le_abs_self _) hz)
          have hmax : max (-L) (e 0 ω) = e 0 ω :=
            max_eq_right (by have := neg_abs_le (e 0 ω); linarith)
          simp [clampAt, hmin, hmax]
        · rcases le_or_gt (e 0 ω) 0 with hz0 | hz0
          · have hzneg : e 0 ω < -L := by rw [abs_of_nonpos hz0] at hz; linarith
            have hmin : min L (e 0 ω) = e 0 ω := min_eq_right (by linarith)
            have hmax : max (-L) (e 0 ω) = -L := max_eq_left (by linarith)
            simp only [clampAt, hmin, hmax]
            rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
            linarith
          · have hzpos : L < e 0 ω := by rw [abs_of_pos hz0] at hz; exact hz
            have hmin : min L (e 0 ω) = L := min_eq_left (by linarith)
            have hmax : max (-L) L = L := max_eq_right (by linarith)
            simp only [clampAt, hmin, hmax]
            rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
            linarith
      linarith
    calc |Fr (X 0 ω, e 0 ω)| ≤ q (e 0 ω) * |W ((X 0 ω - x) / h n)| := h1
      _ ≤ (|e 0 ω| + c) * CW := by
          refine mul_le_mul h2 (hWb _) (abs_nonneg _) (by positivity)
      _ = |CW * (|e 0 ω| + c)| := by
          rw [abs_of_nonneg (mul_nonneg hCW0 (by positivity))]; ring
  have hMemRt : ∀ t : ℤ, MemLp (R t) (ENNReal.ofReal δ) μ := fun t =>
    memLp_comp_pair hmeasX hmeasE hstat t hFrm hMemR0
  have hMemR2 : ∀ t : ℤ, MemLp (R t) 2 μ := fun t => (hMemRt t).mono_exponent hδ2
  have hintR : ∀ s t : ℤ, Integrable (fun ω => R s ω * R t ω) μ :=
    fun s t => (hMemR2 s).integrable_mul (hMemR2 t)
  -- each residual summand is centred
  have hclampint : ∀ t : ℤ, Integrable (fun ω => clampAt L (e t ω)) μ := by
    intro t
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE t)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL0.le _
  have het : ∀ t : ℤ, Integrable (e t) μ := by
    intro t
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => z.2) (X 0 ω, e 0 ω)) 1 μ :=
      memLp_one_iff_integrable.2 he1
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t measurable_snd h0)
  have hcondR : ∀ t : ℤ,
      μ[fun ω => e t ω - clampAt L (e t ω) | MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => -mL (X t ω) := by
    intro t
    have hsub : μ[fun ω => e t ω - clampAt L (e t ω) |
          MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => (μ[e t | MeasurableSpace.comap (X t) inferInstance]) ω
            - (μ[fun ω' => clampAt L (e t ω') |
                MeasurableSpace.comap (X t) inferInstance]) ω :=
      condExp_sub (het t) (hclampint t) _
    have hz := condExp_eq_zero_of_stat hmeasX hmeasE hstat he1 hce t
    filter_upwards [hsub, hz, hmLrep t] with ω h1 h2 h3
    simp only [truncErr] at h3
    have h3' : (μ[fun ω' => clampAt L (e t ω') |
        MeasurableSpace.comap (X t) inferInstance]) ω = mL (X t ω) := by linarith
    have h2' : (μ[e t | MeasurableSpace.comap (X t) inferInstance]) ω = 0 := h2
    rw [h1, h2', h3']
    ring
  have hWXm : ∀ t : ℤ, Measurable (fun ω => W ((X t ω - x) / h n)) := fun t =>
    hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)
  have hmeanR : ∀ t : ℤ, ∫ ω, R t ω ∂μ = 0 := by
    intro t
    have hζi : Integrable (fun ω => e t ω - clampAt L (e t ω)) μ := (het t).sub (hclampint t)
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX t) hζi (hcondR t)
      (fun v => W ((v - x) / h n)) (by fun_prop) (C := CW) (fun v => hWb _)
    have hi1 : Integrable (fun ω => W ((X t ω - x) / h n) * (e t ω - clampAt L (e t ω))) μ :=
      hζi.bdd_mul (hWXm t).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb _)
    have hi2 : Integrable (fun ω => W ((X t ω - x) / h n) * mL (X t ω)) μ := by
      refine (integrable_const (CW * (M * L ^ (1 - δ)))).mono'
        (((hWXm t).mul (hmLm.comp (hmeasX t))).aestronglyMeasurable)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWb _) (hmLB _) (abs_nonneg _) hCW0
    have hsplit : ∫ ω, R t ω ∂μ
        = ∫ ω, W ((X t ω - x) / h n) * (e t ω - clampAt L (e t ω)) ∂μ
          + ∫ ω, W ((X t ω - x) / h n) * mL (X t ω) ∂μ := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [hRdef, hFrdef]; ring)
    have hneg : ∫ ω, W ((X t ω - x) / h n) * (fun ω => -mL (X t ω)) ω ∂μ
        = -∫ ω, W ((X t ω - x) / h n) * mL (X t ω) ∂μ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [hsplit, hz, hneg]
    ring
  -- the lag covariance array
  set Gr : ℕ → ℝ := fun d => ∫ ω, R 0 ω * R (d : ℤ) ω ∂μ with hGrdef
  set Cr : ℕ → ℕ → ℝ := fun s t => ∫ ω, R ((s : ℤ) + 1) ω * R ((t : ℤ) + 1) ω ∂μ with hCrdef
  have hCG : ∀ s d : ℕ, Cr s (s + d) = Gr d := by
    intro s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr := integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
      (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) => Fr z.1 * Fr z.2)
      ((hFrm.comp measurable_fst).mul (hFrm.comp measurable_snd))
    simp only [hCrdef, hGrdef, hRdef, hidx]
    exact htr
  have hCG' : ∀ s d : ℕ, Cr (s + d) s = Gr d := by
    intro s d
    have hsym : Cr (s + d) s = Cr s (s + d) := by
      simp only [hCrdef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  have hexp : ∫ ω, (∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t := by
    have hsq2 : ∀ ω : Ω, (∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ^ 2
        = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
            R ((s : ℤ) + 1) ω * R ((t : ℤ) + 1) ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp only [hsq2, hCrdef]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hintR _ _))]
    exact Finset.sum_congr rfl fun s _ => integral_finset_sum _ (fun t _ => hintR _ _)
  -- conversion of the goal
  have hsqinv : ((Real.sqrt ((n : ℝ) * h n))⁻¹) ^ 2 = ((n : ℝ) * h n)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) (hh0 n).le)]
  have hconv : ∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ
      = ((n : ℝ) * h n)⁻¹ * ∫ ω, (∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range n,
        e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          - truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
            = R ((t : ℤ) + 1) ω :=
      (Filter.eventually_all_finset _).2 (fun t _ => hRrep ((t : ℤ) + 1))
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hall] with ω hω
    simp only [locSum, locTruncSum]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hω, mul_pow, hsqinv]
  -- pointwise facts about the clamp residual
  have habsr : ∀ y : ℝ, |y - clampAt L y| ≤ |y| := by
    intro y
    rcases le_or_gt |y| L with hz | hz
    · have hmin : min L y = y := min_eq_right (le_trans (le_abs_self _) hz)
      have hmax : max (-L) y = y := max_eq_right (by have := neg_abs_le y; linarith)
      simp [clampAt, hmin, hmax]
    · rcases le_or_gt y 0 with hz0 | hz0
      · have hzneg : y < -L := by rw [abs_of_nonpos hz0] at hz; linarith
        have hmin : min L y = y := min_eq_right (by linarith)
        have hmax : max (-L) y = -L := max_eq_left (by linarith)
        simp only [clampAt, hmin, hmax]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
        linarith
      · have hzpos : L < y := by rw [abs_of_pos hz0] at hz; exact hz
        have hmin : min L y = L := min_eq_left (by linarith)
        have hmax : max (-L) L = L := max_eq_right (by linarith)
        simp only [clampAt, hmin, hmax]
        rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
        linarith
  have hc2 : c ^ 2 = M ^ 2 * L ^ (2 - 2 * δ) := by
    have hkey : (L ^ (1 - δ)) ^ (2 : ℕ) = L ^ (2 - 2 * δ) := by
      rw [← Real.rpow_natCast (L ^ (1 - δ)) 2, ← Real.rpow_mul hL0.le]
      norm_num
      ring_nf
    rw [hcdef, mul_pow, hkey]
  have he2 : Integrable (fun ω => e 0 ω ^ 2) μ := (heLδ.mono_exponent hδ2).integrable_sq
  -- diagonal
  have hiA : Integrable
      (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / h n) ^ 2) μ := by
    refine Integrable.mono ((heδi.const_mul (L ^ (2 - δ))).const_mul (CW ^ 2))
      ((((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0))).pow_const 2).mul
        ((hWXm 0).pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ 2 * (L ^ (2 - δ) * |e 0 ω| ^ δ))]
    have h1 := sq_sub_clamp_le (δ := δ) (L := L) (z := e 0 ω) hδ hL0
    have h2 : W ((X 0 ω - x) / h n) ^ 2 ≤ CW ^ 2 := by
      have := hWb ((X 0 ω - x) / h n)
      nlinarith [sq_abs (W ((X 0 ω - x) / h n)), abs_nonneg (W ((X 0 ω - x) / h n))]
    nlinarith [sq_nonneg (e 0 ω - clampAt L (e 0 ω)), sq_nonneg (W ((X 0 ω - x) / h n)),
      Real.rpow_nonneg (abs_nonneg (e 0 ω)) δ, Real.rpow_nonneg hL0.le (2 - δ)]
  have hiB : Integrable (fun ω => W ((X 0 ω - x) / h n) ^ 2) μ := by
    refine (integrable_const (CW ^ 2)).mono' ((hWXm 0).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hWb ((X 0 ω - x) / h n)
    nlinarith [sq_abs (W ((X 0 ω - x) / h n)), abs_nonneg (W ((X 0 ω - x) / h n))]
  have hres := localized_trunc_residual_moment_le (X := X) (e := e) (hmeasX 0) (hmeasE 0)
    hmp hp0 hpd hδ heLδ heδc hpb hWm hWb hW2 (x := x) (hn := h n) (hh0 n) hL0
  have hwt := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
    (G := fun v => W v ^ 2) (hWm.pow_const 2) (fun v => sq_nonneg _) hW2 (x := x) (hh0 n)
  have hdiagR : |Gr 0|
      ≤ (2 * (M * Cp * IW2) * L ^ (2 - δ) + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ))
        * h n := by
    have hGeq : Gr 0 = ∫ ω, (R 0 ω) ^ 2 ∂μ := by
      simp only [hGrdef, Nat.cast_zero]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hGnn : 0 ≤ Gr 0 := by rw [hGeq]; exact integral_nonneg fun ω => sq_nonneg _
    have hmaj : ∫ ω, (R 0 ω) ^ 2 ∂μ
        ≤ 2 * ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
          + 2 * c ^ 2 * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hiA.const_mul 2)
        (hiB.const_mul (2 * c ^ 2))]
      refine integral_mono (hMemR2 0).integrable_sq
        ((hiA.const_mul 2).add (hiB.const_mul (2 * c ^ 2))) fun ω => ?_
      have hb := hmLB (X 0 ω)
      have hb2 : mL (X 0 ω) ^ 2 ≤ c ^ 2 := by
        rw [hcdef] at hb ⊢
        nlinarith [abs_nonneg (mL (X 0 ω)), sq_abs (mL (X 0 ω))]
      simp only [hRdef, hFrdef, mul_pow]
      nlinarith [sq_nonneg (W ((X 0 ω - x) / h n)),
        sq_nonneg ((e 0 ω - clampAt L (e 0 ω)) - mL (X 0 ω)),
        sq_nonneg ((e 0 ω - clampAt L (e 0 ω)) + mL (X 0 ω))]
    rw [abs_of_nonneg hGnn, hGeq]
    refine hmaj.trans ?_
    have hstep1 : 2 * ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
        ≤ 2 * ((M * Cp * IW2) * (L ^ (2 - δ) * h n)) := by
      have : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left hres this
    have hstep2 : 2 * c ^ 2 * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ
        ≤ 2 * c ^ 2 * ((Cp * IW2) * h n) :=
      mul_le_mul_of_nonneg_left hwt (by positivity)
    rw [hc2] at hstep2
    rw [hc2]
    refine le_trans (add_le_add hstep1 hstep2) (le_of_eq ?_)
    ring
  -- small lags
  have hqsqle : ∀ y : ℝ, q y ^ 2 ≤ 2 * (y - clampAt L y) ^ 2 + 2 * c ^ 2 := by
    intro y
    have h1 : q y = |y - clampAt L y| + c := rfl
    rw [h1]
    nlinarith [sq_abs (y - clampAt L y), sq_nonneg (|y - clampAt L y| - c)]
  have hqsqle2 : ∀ y : ℝ, q y ^ 2 ≤ 2 * y ^ 2 + 2 * c ^ 2 := by
    intro y
    refine (hqsqle y).trans ?_
    have h2 := habsr y
    nlinarith [sq_abs (y - clampAt L y), sq_abs y, abs_nonneg (y - clampAt L y), abs_nonneg y]
  have hiq2 : ∀ t : ℤ, Integrable (fun ω => q (e t ω) ^ 2) μ := by
    intro t
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => q z.2 ^ 2) (X 0 ω, e 0 ω)) 1 μ := by
      refine memLp_one_iff_integrable.2 ?_
      refine Integrable.mono ((he2.const_mul 2).add (integrable_const (2 * c ^ 2)))
        (((hqm.comp (hmeasE 0)).pow_const 2)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * e 0 ω ^ 2 + 2 * c ^ 2)]
      exact hqsqle2 (e 0 ω)
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t ((hqm.comp measurable_snd).pow_const 2) h0)
  have hq2eq : ∀ t : ℤ, ∫ ω, q (e t ω) ^ 2 ∂μ = ∫ ω, q (e 0 ω) ^ 2 ∂μ := fun t =>
    integral_comp_pair_eq hmeasX hmeasE hstat t
      (F := fun z : ℝ × ℝ => q z.2 ^ 2) ((hqm.comp measurable_snd).pow_const 2)
  have hressq : ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 ∂μ ≤ L ^ (2 - δ) * Eδ := by
    have hi1 : Integrable (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2) μ := by
      refine Integrable.mono he2
        ((((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0)))).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      have := habsr (e 0 ω)
      nlinarith [sq_abs (e 0 ω - clampAt L (e 0 ω)), sq_abs (e 0 ω),
        abs_nonneg (e 0 ω - clampAt L (e 0 ω)), abs_nonneg (e 0 ω)]
    have hi2 : Integrable (fun ω => L ^ (2 - δ) * |e 0 ω| ^ δ) μ := heδi.const_mul _
    calc ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 ∂μ
        ≤ ∫ ω, L ^ (2 - δ) * |e 0 ω| ^ δ ∂μ :=
          integral_mono hi1 hi2 (fun ω => sq_sub_clamp_le hδ hL0)
      _ = L ^ (2 - δ) * Eδ := by rw [integral_const_mul]
  have hq2int : ∫ ω, q (e 0 ω) ^ 2 ∂μ ≤ 2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2 := by
    have hi1 : Integrable (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2) μ := by
      refine Integrable.mono he2
        ((((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0)))).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      have := habsr (e 0 ω)
      nlinarith [sq_abs (e 0 ω - clampAt L (e 0 ω)), sq_abs (e 0 ω),
        abs_nonneg (e 0 ω - clampAt L (e 0 ω)), abs_nonneg (e 0 ω)]
    have hi3 : Integrable (fun ω => 2 * (e 0 ω - clampAt L (e 0 ω)) ^ 2 + 2 * c ^ 2) μ :=
      (hi1.const_mul 2).add (integrable_const (2 * c ^ 2))
    calc ∫ ω, q (e 0 ω) ^ 2 ∂μ
        ≤ ∫ ω, (2 * (e 0 ω - clampAt L (e 0 ω)) ^ 2 + 2 * c ^ 2) ∂μ :=
          integral_mono (hiq2 0) hi3 (fun ω => hqsqle (e 0 ω))
      _ = 2 * ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 ∂μ + 2 * c ^ 2 := by
          rw [integral_add (hi1.const_mul 2) (integrable_const (2 * c ^ 2)),
            integral_const_mul]
          simp
      _ ≤ 2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2 := by linarith
  have hsmallR : ∀ j : ℕ, 1 ≤ j →
      |Gr j| ≤ B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2 := by
    intro j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    have hfm : Measurable (fun z : ℝ × ℝ => q z.1 * q z.2) :=
      (hqm.comp measurable_fst).mul (hqm.comp measurable_snd)
    have hgm : Measurable
        (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|) := by fun_prop
    have hg0 : ∀ z : ℝ × ℝ, 0 ≤ |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)| :=
      fun z => by positivity
    have hRHSi : Integrable (fun ω => |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| *
        (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
          (X 0 ω, X (j : ℤ) ω)) μ := by
      refine Integrable.mono
        (((hiq2 0).const_mul (CW ^ 2)).add ((hiq2 (j : ℤ)).const_mul (CW ^ 2)))
        ((((hfm.comp ((hmeasE 0).prodMk (hmeasE (j : ℤ)))).abs).mul
          (hgm.comp ((hmeasX 0).prodMk (hmeasX (j : ℤ)))))).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have hq00 : 0 ≤ q (e 0 ω) := hq0 _
      have hqj0 : 0 ≤ q (e (j : ℤ) ω) := hq0 _
      have hw0 := hWb ((X 0 ω - x) / h n)
      have hwj := hWb ((X (j : ℤ) ω - x) / h n)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |q (e 0 ω) * q (e (j : ℤ) ω)| *
        (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ 2 * q (e 0 ω) ^ 2 +
          CW ^ 2 * q (e (j : ℤ) ω) ^ 2),
        abs_of_nonneg (mul_nonneg hq00 hqj0)]
      have hprodW : |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ≤ CW ^ 2 := by
        nlinarith [abs_nonneg (W ((X 0 ω - x) / h n)), abs_nonneg (W ((X (j : ℤ) ω - x) / h n))]
      nlinarith [sq_nonneg (q (e 0 ω) - q (e (j : ℤ) ω)), mul_nonneg hq00 hqj0]
    have hA : |Gr j| ≤ ∫ ω, |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| *
        (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
          (X 0 ω, X (j : ℤ) ω) ∂μ := by
      have h0 := norm_integral_le_integral_norm (μ := μ) (fun ω => R 0 ω * R (j : ℤ) ω)
      simp only [Real.norm_eq_abs] at h0
      refine (le_trans h0 ?_)
      refine integral_mono (hintR 0 (j : ℤ)).abs hRHSi fun ω => ?_
      have hb0 := hFrb (X 0 ω, e 0 ω)
      have hbj := hFrb (X (j : ℤ) ω, e (j : ℤ) ω)
      simp only [hRdef, abs_mul]
      rw [abs_of_nonneg (hq0 (e 0 ω)), abs_of_nonneg (hq0 (e (j : ℤ) ω))]
      calc |Fr (X 0 ω, e 0 ω)| * |Fr (X (j : ℤ) ω, e (j : ℤ) ω)|
          ≤ (q (e 0 ω) * |W ((X 0 ω - x) / h n)|) *
            (q (e (j : ℤ) ω) * |W ((X (j : ℤ) ω - x) / h n)|) :=
            mul_le_mul hb0 hbj (abs_nonneg _) (by positivity)
        _ = q (e 0 ω) * q (e (j : ℤ) ω) *
            (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by ring
    have hC2 := hC2gen (j : ℤ) hjz (fun z : ℝ × ℝ => q z.1 * q z.2) hfm _ hgm hg0
    refine hA.trans (hC2.trans ?_)
    have hfint : ∫ ω, |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| ∂μ
        ≤ 2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2 := by
      have hi : Integrable (fun ω => |q (e 0 ω) * q (e (j : ℤ) ω)|) μ := by
        refine Integrable.mono (((hiq2 0).add (hiq2 (j : ℤ))).div_const 2)
          ((((hqm.comp (hmeasE 0)).mul (hqm.comp (hmeasE (j : ℤ)))).abs)).aestronglyMeasurable
          (Eventually.of_forall fun ω => ?_)
        simp only [Pi.add_apply, Real.norm_eq_abs]
        rw [abs_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤
          (q (e 0 ω) ^ 2 + q (e (j : ℤ) ω) ^ 2) / 2),
          abs_of_nonneg (mul_nonneg (hq0 _) (hq0 _))]
        nlinarith [sq_nonneg (q (e 0 ω) - q (e (j : ℤ) ω))]
      have hstep : ∫ ω, |q (e 0 ω) * q (e (j : ℤ) ω)| ∂μ
          ≤ ∫ ω, (q (e 0 ω) ^ 2 + q (e (j : ℤ) ω) ^ 2) / 2 ∂μ := by
        refine integral_mono hi (((hiq2 0).add (hiq2 (j : ℤ))).div_const 2) fun ω => ?_
        rw [abs_of_nonneg (mul_nonneg (hq0 _) (hq0 _))]
        nlinarith [sq_nonneg (q (e 0 ω) - q (e (j : ℤ) ω))]
      have heval : ∫ ω, (q (e 0 ω) ^ 2 + q (e (j : ℤ) ω) ^ 2) / 2 ∂μ
          = ∫ ω, q (e 0 ω) ^ 2 ∂μ := by
        rw [integral_div, integral_add (hiq2 0) (hiq2 (j : ℤ)), hq2eq (j : ℤ)]
        ring
      simp only
      rw [heval] at hstep
      exact hstep.trans hq2int
    have hprodg : ∫ z : ℝ × ℝ, |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|
          ∂(MeasureTheory.volume.prod MeasureTheory.volume)
        = (∫ v, |W ((v - x) / h n)|) * ∫ w, |W ((w - x) / h n)| :=
      integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (f := fun v => |W ((v - x) / h n)|) (g := fun w => |W ((w - x) / h n)|)
    have honeW : ∫ v, |W ((v - x) / h n)| = h n * IW := by
      have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x (hh0 n)
      simp only [mul_one] at this
      rw [hIWdef, this, ← mul_assoc, mul_inv_cancel₀ (hh0 n).ne', one_mul]
    rw [hprodg, honeW]
    have hnn : (0 : ℝ) ≤ (h n * IW) * (h n * IW) :=
      mul_nonneg (mul_nonneg (hh0 n).le hIW0) (mul_nonneg (hh0 n).le hIW0)
    have hB2 : (0 : ℝ) ≤ B := hB0
    calc B * (∫ ω, |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| ∂μ)
          * ((h n * IW) * (h n * IW))
        ≤ B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * ((h n * IW) * (h n * IW)) := by
          gcongr
      _ = B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2 := by ring
  -- the localized δ-th moment of the residual array
  have hpow2 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ δ ≤ 2 ^ δ * (a ^ δ + b ^ δ) := by
    intro a b ha hb
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ δ := Real.rpow_nonneg (by norm_num) _
    have h5a : (0 : ℝ) ≤ a ^ δ := Real.rpow_nonneg ha _
    have h5b : (0 : ℝ) ≤ b ^ δ := Real.rpow_nonneg hb _
    rcases le_total a b with hab | hab
    · have h1 : a + b ≤ 2 * b := by linarith
      have h3 := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ a + b) h1 hδ0.le
      rw [Real.mul_rpow (by norm_num) hb] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h5a) h4)
    · have h1 : a + b ≤ 2 * a := by linarith
      have h3 := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ a + b) h1 hδ0.le
      rw [Real.mul_rpow (by norm_num) ha] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h5b) h4)
  have hGm2 : Measurable (fun v => |W ((v - x) / h n)| ^ δ) :=
    hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
  have hGXm2 : Measurable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) := hGm2.comp (hmeasX 0)
  have hiW1 : Integrable (fun ω => |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ) μ := by
    refine Integrable.mono (heδi.const_mul (CW ^ δ))
      ((hrp.comp (((hmeasE 0).mul (hWXm 0)).abs))).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ δ * |e 0 ω| ^ δ), abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm (CW ^ δ)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le) (Real.rpow_nonneg (abs_nonneg _) _)
  have hiW2 : Integrable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) μ := by
    refine (integrable_const (CW ^ δ)).mono' hGXm2.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le
  have hdeltaR : ∫ ω, |R 0 ω| ^ δ ∂μ ≤ Kρ * h n := by
    have hbd : ∀ ω, |R 0 ω| ^ δ
        ≤ 2 ^ δ * (|e 0 ω * W ((X 0 ω - x) / h n)| ^ δ
            + M ^ δ * |W ((X 0 ω - x) / h n)| ^ δ) := by
      intro ω
      have h1 : |R 0 ω| ≤ (|e 0 ω| + M) * |W ((X 0 ω - x) / h n)| := by
        refine le_trans (hFrb (X 0 ω, e 0 ω)) ?_
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h2 : q (e 0 ω) = |e 0 ω - clampAt L (e 0 ω)| + c := rfl
        have h3 := habsr (e 0 ω)
        rw [h2]; linarith
      have h4 : |R 0 ω| ^ δ ≤ ((|e 0 ω| + M) * |W ((X 0 ω - x) / h n)|) ^ δ :=
        Real.rpow_le_rpow (abs_nonneg _) h1 hδ0.le
      refine h4.trans ?_
      rw [Real.mul_rpow (by positivity) (abs_nonneg _)]
      have h5 := hpow2 (|e 0 ω|) M (abs_nonneg _) hM0
      have h6 : |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ
          = |e 0 ω| ^ δ * |W ((X 0 ω - x) / h n)| ^ δ := by
        rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      rw [h6]
      have h7 : (0 : ℝ) ≤ |W ((X 0 ω - x) / h n)| ^ δ := Real.rpow_nonneg (abs_nonneg _) _
      nlinarith [h5, h7]
    have hmaji : Integrable (fun ω => 2 ^ δ * (|e 0 ω * W ((X 0 ω - x) / h n)| ^ δ
        + M ^ δ * |W ((X 0 ω - x) / h n)| ^ δ)) μ :=
      (hiW1.add (hiW2.const_mul (M ^ δ))).const_mul (2 ^ δ)
    have hRi : Integrable (fun ω => |R 0 ω| ^ δ) μ := by
      refine Integrable.mono hmaji ((hrp.comp (hRm 0).abs)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ δ *
          (|e 0 ω * W ((X 0 ω - x) / h n)| ^ δ + M ^ δ * |W ((X 0 ω - x) / h n)| ^ δ))]
      exact hbd ω
    have hstep : ∫ ω, |R 0 ω| ^ δ ∂μ
        ≤ 2 ^ δ * (∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ
            + M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ) := by
      have := integral_mono hRi hmaji hbd
      rwa [integral_const_mul, integral_add hiW1 (hiW2.const_mul (M ^ δ)),
        integral_const_mul] at this
    have hd1 := localized_delta_moment_le (X := X) (e := e) (hmeasX 0) hmp hp0 hpd hδ heLδ
      heδc hpb hWm hWb hW2 (x := x) (hn := h n) (hh0 n)
    have hd2 := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => |W v| ^ δ) hWam (fun v => Real.rpow_nonneg (abs_nonneg _) _) hWδ
      (x := x) (hh0 n)
    refine hstep.trans ?_
    have h2δ : (0 : ℝ) ≤ (2 : ℝ) ^ δ := Real.rpow_nonneg (by norm_num) _
    have hMδ : (0 : ℝ) ≤ M ^ δ := Real.rpow_nonneg hM0 _
    rw [hKρdef]
    have hA : ∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ
          + M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
        ≤ (M * Cp * IWδ) * h n + M ^ δ * ((Cp * IWδ) * h n) := by
      have hb1 : ∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ ≤ (M * Cp * IWδ) * h n := hd1
      have hb2 : M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
          ≤ M ^ δ * ((Cp * IWδ) * h n) := mul_le_mul_of_nonneg_left hd2 hMδ
      linarith
    calc (2 : ℝ) ^ δ * (∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ
            + M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ)
        ≤ 2 ^ δ * ((M * Cp * IWδ) * h n + M ^ δ * ((Cp * IWδ) * h n)) :=
          mul_le_mul_of_nonneg_left hA h2δ
      _ = 2 ^ δ * (M + M ^ δ) * (Cp * IWδ) * h n := by ring
  -- Davydov
  have hnormδR : ∀ t : ℤ, (eLpNorm (R t) (ENNReal.ofReal δ) μ).toReal ≤ (Kρ * h n) ^ (1 / δ) := by
    intro t
    have hEq : eLpNorm (R t) (ENNReal.ofReal δ) μ = eLpNorm (R 0) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t hFrm _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := hMemR0.eLpNorm_eq_integral_rpow_norm hp1 ENNReal.ofReal_ne_top
    have hb0 : (0 : ℝ) ≤ ∫ a, ‖R 0 a‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hb0 _), ← one_div]
    have hnn : ∫ a, ‖R 0 a‖ ^ δ ∂μ ≤ Kρ * h n := by
      simpa only [Real.norm_eq_abs] using hdeltaR
    exact Real.rpow_le_rpow hb0 hnn (by positivity)
  have hlargeR : ∀ j : ℕ, 1 ≤ j →
      |Gr j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kρ * h n) ^ (2 / δ) := by
    intro j hj
    have hcov : cov[R 0, R (j : ℤ); μ] = Gr j := by
      rw [covariance_eq_sub (hMemR2 0) (hMemR2 (j : ℤ)), hmeanR 0, zero_mul, sub_zero]
      simp only [hGrdef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound' hmeasX hmeasE hδ hFrm j hj
      (hMemRt 0) (hMemRt (j : ℤ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ Kρ * h n := mul_nonneg hKρ0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (Kρ * h n) ^ (2 / δ) = (Kρ * h n) ^ (1 / δ) * (Kρ * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδR 0
    · exact hnormδR (j : ℤ)
  -- the lag-sum split at `m_n`
  have hposL : (0 : ℝ) < h n * |Real.log (h n)| := mul_pos (hh0 n) hlogn
  have hm1 : 1 ≤ smallLagCut h n := Nat.ceil_pos.2 (by positivity)
  have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
  have hlagsum : ∑ j ∈ Finset.Ico 1 n, |Gr j|
      ≤ (smallLagCut h n : ℝ) * (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2)
        + 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gr j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gr j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gr j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gr j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gr j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gr j|
        ≤ (smallLagCut h n : ℝ) *
          (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gr j|) (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2)
        (fun j hj => hsmallR j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gr j|
        ≤ 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (Kρ * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hKρ0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gr j| ≤ 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
            ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
        have hj1' : 1 ≤ j := by omega
        refine (hlargeR j hj1').trans ?_
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
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kρ * h n) ^ (2 / δ)
            = 8 * (Kρ * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (Kρ * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by gcongr
          _ = 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  have hmb : (smallLagCut h n : ℝ) ^ (-lam) ≤ (h n * |Real.log (h n)|) ^ lam := by
    have hmge : (h n * |Real.log (h n)|)⁻¹ ≤ (smallLagCut h n : ℝ) := Nat.le_ceil _
    have hmlam : (0 : ℝ) < (smallLagCut h n : ℝ) ^ lam := Real.rpow_pos_of_pos hmR _
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
  -- final assembly
  rw [hconv, hexp]
  have habs := abs_double_sum_subset_le (n := n) (Finset.range n) (Finset.Subset.refl _)
    (Cr) (Gr) hCG hCG'
  rw [Finset.card_range] at habs
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hhn : 0 < h n := hh0 n
  have hkey : ((n : ℝ) * h n)⁻¹ * (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t)
      ≤ (h n)⁻¹ * |Gr 0| + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gr j| := by
    calc ((n : ℝ) * h n)⁻¹ * (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t)
        ≤ ((n : ℝ) * h n)⁻¹ * |∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ ((n : ℝ) * h n)⁻¹ *
            ((n : ℝ) * (|Gr 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |Gr j|)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (h n)⁻¹ * |Gr 0| + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gr j| := by
          field_simp
  refine hkey.trans ?_
  have hLt1 : (0 : ℝ) ≤ L ^ (2 - δ) := Real.rpow_nonneg hL0.le _
  have hLt2 : (0 : ℝ) ≤ L ^ (2 - 2 * δ) := Real.rpow_nonneg hL0.le _
  have hx1 : (0 : ℝ) ≤ 4 * B * IW ^ 2 * Eδ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) (sq_nonneg IW)) hEδ0
  have hx2 : (0 : ℝ) ≤ 4 * B * IW ^ 2 * M ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) (sq_nonneg IW)) (sq_nonneg M)
  have hA1 : (h n)⁻¹ * |Gr 0|
      ≤ (2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ) := by
    have h1 : (h n)⁻¹ * |Gr 0|
        ≤ (h n)⁻¹ * ((2 * (M * Cp * IW2) * L ^ (2 - δ)
            + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ)) * h n) :=
      mul_le_mul_of_nonneg_left hdiagR (by positivity)
    have h2 : (h n)⁻¹ * ((2 * (M * Cp * IW2) * L ^ (2 - δ)
          + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ)) * h n)
        = 2 * (M * Cp * IW2) * L ^ (2 - δ) + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ) := by
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    nlinarith [mul_nonneg hx1 hLt1, mul_nonneg hx2 hLt2]
  have hA2 : 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gr j|
      ≤ ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
          + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
          * ((smallLagCut h n : ℝ) * h n)
        + 16 * SA * Kρ ^ (2 / δ) * (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
    have hmul := mul_le_mul_of_nonneg_left hlagsum (by positivity : (0 : ℝ) ≤ 2 * (h n)⁻¹)
    refine hmul.trans ?_
    rw [mul_add]
    have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) *
          (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2))
        = (2 * B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * IW ^ 2) *
          ((smallLagCut h n : ℝ) * h n) := by
      field_simp
    have hmh : (0 : ℝ) ≤ (smallLagCut h n : ℝ) * h n := by positivity
    have e1' : (2 * B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * IW ^ 2) *
          ((smallLagCut h n : ℝ) * h n)
        ≤ ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
          + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
          * ((smallLagCut h n : ℝ) * h n) := by
      refine mul_le_mul_of_nonneg_right ?_ hmh
      rw [hc2]
      have hy1 : (0 : ℝ) ≤ 2 * M * Cp * IW2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hCp0) hIW20
      have hy2 : (0 : ℝ) ≤ 2 * M ^ 2 * Cp * IW2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) hCp0) hIW20
      nlinarith [mul_nonneg hy1 hLt1, mul_nonneg hy2 hLt2]
    have hKrw : (Kρ * h n) ^ (2 / δ) = Kρ ^ (2 / δ) * (h n) ^ (2 / δ) :=
      Real.mul_rpow hKρ0 hhn.le
    have hLrw : (h n * |Real.log (h n)|) ^ lam
        = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
    have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
      rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
        Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
    have hKh : (0 : ℝ) ≤ (Kρ * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hKρ0 hhn.le) _
    have e2 : 2 * (h n)⁻¹ * (8 * (Kρ * h n) ^ (2 / δ) *
          ((smallLagCut h n : ℝ) ^ (-lam) * SA))
        ≤ 16 * SA * Kρ ^ (2 / δ) * ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
      calc 2 * (h n)⁻¹ *
            (8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ 2 * (h n)⁻¹ * (8 * (Kρ * h n) ^ (2 / δ) *
              ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
        _ = 16 * SA * Kρ ^ (2 / δ) *
              ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
            rw [hKrw, hLrw, hpow]; ring
    rw [e1]
    linarith
  have hfinal : ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
        * (1 + (smallLagCut h n : ℝ) * h n)
      = ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
        + ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
          * ((smallLagCut h n : ℝ) * h n) := by ring
  rw [hfinal]
  linarith

end StatLean.TimeSeries
