import StatLean.TimeSeries.Spectral.SpectralDensity

/-!
# Linear filters and the input–output spectral relation (FY §2.3.3, Theorem 2.12)

**Definition 2.7** (two-sided linear filter with `ℓ¹` coefficients, as an `L²`-limit —
the convergence mode FY leaves implicit), the **transfer function**
`Γ(λ) = Σ_{k ∈ ℤ} φ_k e^{−ikλ}`, and **FY Theorem 2.12** with the inventory's
hypothesis-discipline upgrades: for a stationary input with summable ACVF and an `ℓ¹`
filter, the output is stationary (derived, not assumed), its ACVF is the double
convolution `γ_X(k) = Σ_{j,l} φ_j φ_l γ_Y(k + j − l)` and is summable (derived — FY
assumes it), and the spectral densities satisfy `g_X = |Γ|² g_Y` pointwise.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.3,
Definition 2.7 (eqs. (2.41)–(2.42)), Theorem 2.12 with in-text proof (pp. 55–56).
(`FY §2.3.3 Def 2.7, Thm 2.12`.)

**Proof formalization notes.** Well-definedness (existence of the `L²`-limits) mirrors
the one-sided `Process/LinearProcess.lean` development with two-sided symmetric partial
sums `Σ_{|k| ≤ N}`; the ACVF convolution passes `L²`-continuity of covariance through
the double series (Fubini for absolutely convergent double sums,
`Summable.tsum_comm`-family); the density identity is the triple-series rearrangement of
FY's proof, executed on the series side of `spectralDensityOf`.

**Bibliographic comments.** Linear filtering of stationary processes is classical
Wiener–Kolmogorov theory; FY follow Brockwell & Davis (1991), Thm 4.4.1.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Two-sided linear filter** (FY Definition 2.7, eq. (2.41)): `X_t = Σ_{k ∈ ℤ} φ_k
Y_{t−k}` as an `L²`-limit of the symmetric partial sums. -/
def IsFilteredBy (X Y : ℤ → Ω → ℝ) (φ : ℤ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N : ℕ => eLpNorm
      (fun ω => X t ω - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ k * Y (t - k) ω) 2 μ)
    atTop (nhds 0)

/-- The **transfer function** `Γ(λ) = Σ_{k ∈ ℤ} φ_k e^{−ikλ}` (FY §2.3.3; junk when
`φ ∉ ℓ¹` by the `tsum` convention). -/
noncomputable def transferFun (φ : ℤ → ℝ) (l : AddCircle (2 * π)) : ℂ :=
  ∑' k : ℤ, (φ k : ℂ) * fourier (-k) l

section Aux

variable {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul, h1, h2]

/-- The symmetric partial sum `Σ_{|k| ≤ N} φ_k Y_{t−k}` of the filter. -/
private noncomputable def fpsum (φ : ℤ → ℝ) (Y : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ k * Y (t - k) ω

private lemma memLp_fpsum (hY : IsStationary Y μ) (t : ℤ) (N : ℕ) :
    MemLp (fpsum φ Y t N) 2 μ :=
  memLp_finset_sum _ fun k _ => (hY.memLp (t - k)).const_mul (φ k)

private noncomputable def fpsumLp (hY : IsStationary Y μ) (φ : ℤ → ℝ) (t : ℤ) (N : ℕ) :
    Lp ℝ 2 μ := (memLp_fpsum (φ := φ) hY t N).toLp _

private lemma coeFn_fpsumLp (hY : IsStationary Y μ) (φ : ℤ → ℝ) (t : ℤ) (N : ℕ) :
    ⇑(fpsumLp hY φ t N) =ᵐ[μ] fpsum φ Y t N :=
  (memLp_fpsum (φ := φ) hY t N).coeFn_toLp

/-- The second moment of the input does not depend on time. -/
private lemma integral_sq_stationary [IsProbabilityMeasure μ] (hY : IsStationary Y μ) (s : ℤ) :
    ∫ ω, Y s ω * Y s ω ∂μ = acvf Y μ 0 + (∫ ω, Y 0 ω ∂μ) ^ 2 := by
  have h := covariance_eq_sub (hY.memLp s) (hY.memLp s)
  have hcov : cov[Y s, Y s; μ] = acvf Y μ 0 := by
    have h1 := hY.cov_eq_acvf s s
    rwa [sub_self] at h1
  have hmul : μ[Y s * Y s] = ∫ ω, Y s ω * Y s ω ∂μ := by simp [Pi.mul_apply]
  rw [hcov, hmul, hY.integral_eq s 0] at h
  have hsq : (∫ ω, Y 0 ω ∂μ) ^ 2 = (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ) := sq _
  linarith

/-- The common `L²` norm of the input marginals. -/
private noncomputable def inputNorm (Y : ℤ → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  Real.sqrt (acvf Y μ 0 + (∫ ω, Y 0 ω ∂μ) ^ 2)

private lemma norm_YLp [IsProbabilityMeasure μ] (hY : IsStationary Y μ) (s : ℤ) :
    ‖(hY.memLp s).toLp (Y s)‖ = inputNorm Y μ := by
  have h : ‖(hY.memLp s).toLp (Y s)‖ ^ 2 = acvf Y μ 0 + (∫ ω, Y 0 ω ∂μ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp, integral_sq_stationary hY s]
  have h2 := Real.sqrt_sq (norm_nonneg ((hY.memLp s).toLp (Y s)))
  rw [h] at h2
  exact h2.symm

private lemma Icc_int_succ (N : ℕ) :
    Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      = insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- Passing from `N` to `N + 1` adds the two extreme terms. -/
private lemma fpsum_succ (φ : ℤ → ℝ) (Y : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) (ω : Ω) :
    fpsum φ Y t (N + 1) ω
      = φ (-((N : ℤ) + 1)) * Y (t + ((N : ℤ) + 1)) ω
        + (φ ((N : ℤ) + 1) * Y (t - ((N : ℤ) + 1)) ω + fpsum φ Y t N ω) := by
  simp only [fpsum]
  rw [show ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 by push_cast; ring, Icc_int_succ N,
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [show t - -((N : ℤ) + 1) = t + ((N : ℤ) + 1) by ring]

private lemma fpsumLp_succ (hY : IsStationary Y μ) (φ : ℤ → ℝ) (t : ℤ) (N : ℕ) :
    fpsumLp hY φ t (N + 1)
      = φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
        + (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))
          + fpsumLp hY φ t N) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fpsumLp hY φ t (N + 1), coeFn_fpsumLp hY φ t N,
    Lp.coeFn_add (φ (-((N : ℤ) + 1)) •
        (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1))))
      (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))
        + fpsumLp hY φ t N),
    Lp.coeFn_add (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1))))
      (fpsumLp hY φ t N),
    Lp.coeFn_smul (φ (-((N : ℤ) + 1)))
      ((hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))),
    Lp.coeFn_smul (φ ((N : ℤ) + 1))
      ((hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))),
    (hY.memLp (t + ((N : ℤ) + 1))).coeFn_toLp, (hY.memLp (t - ((N : ℤ) + 1))).coeFn_toLp]
    with ω h1 h2 h3 h4 h5 h6 h7 h8
  simp only [h1, h3, h4, h5, h6, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h7, h8, h2]
  exact fpsum_succ φ Y t N ω

private lemma dist_fpsumLp_succ [IsProbabilityMeasure μ] (hY : IsStationary Y μ) (φ : ℤ → ℝ)
    (t : ℤ) (N : ℕ) :
    dist (fpsumLp hY φ t N) (fpsumLp hY φ t (N + 1))
      ≤ (|φ (-((N : ℤ) + 1))| + |φ ((N : ℤ) + 1)|) * inputNorm Y μ := by
  rw [dist_comm, dist_eq_norm, fpsumLp_succ]
  have hcancel : (φ (-((N : ℤ) + 1)) •
        (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
      + (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))
        + fpsumLp hY φ t N)) - fpsumLp hY φ t N
      = φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
        + φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1))) := by
    abel
  rw [hcancel]
  calc ‖φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
          + φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))‖
      ≤ ‖φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))‖
        + ‖φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))‖ :=
        norm_add_le _ _
    _ = (|φ (-((N : ℤ) + 1))| + |φ ((N : ℤ) + 1)|) * inputNorm Y μ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_YLp hY,
          norm_YLp hY]
        ring

private lemma summable_shift_pos (hφ : Summable fun k : ℤ => |φ k|) :
    Summable fun N : ℕ => |φ ((N : ℤ) + 1)| :=
  hφ.comp_injective (fun a b hab => by omega)

private lemma summable_shift_neg (hφ : Summable fun k : ℤ => |φ k|) :
    Summable fun N : ℕ => |φ (-((N : ℤ) + 1))| :=
  hφ.comp_injective (fun a b hab => by omega)

end Aux

/-- **Existence of the filtered process** (the well-definedness FY glosses): an `ℓ¹`
filter applied to a weakly stationary input admits an `L²` output. -/
theorem exists_isFilteredBy [IsProbabilityMeasure μ] {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hmeas : ∀ t, Measurable (Y t)) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ IsFilteredBy X Y φ μ := by
  have main : ∀ t : ℤ, ∃ f : Ω → ℝ, Measurable f ∧
      Tendsto (fun N => eLpNorm (fun ω => f ω - fpsum φ Y t N ω) 2 μ) atTop (nhds 0) := by
    intro t
    have hsum : Summable fun N : ℕ => dist (fpsumLp hY φ t N) (fpsumLp hY φ t N.succ) := by
      refine Summable.of_nonneg_of_le (fun N => dist_nonneg)
        (fun N => dist_fpsumLp_succ hY φ t N) ?_
      exact ((summable_shift_neg hφ).add (summable_shift_pos hφ)).mul_right _
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
    refine ⟨(Lp.aestronglyMeasurable L).mk _,
      (Lp.aestronglyMeasurable L).stronglyMeasurable_mk.measurable, ?_⟩
    have heq : ∀ N : ℕ,
        eLpNorm (fun ω => ((Lp.aestronglyMeasurable L).mk _) ω - fpsum φ Y t N ω) 2 μ
          = edist (fpsumLp hY φ t N) L := by
      intro N
      rw [edist_comm, Lp.edist_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(Lp.aestronglyMeasurable L).ae_eq_mk, coeFn_fpsumLp hY φ t N]
        with ω h1 h2
      simp only [Pi.sub_apply, ← h1, h2]
    simp_rw [heq, edist_dist]
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hL)
  choose X hXm hXlim using main
  exact ⟨X, hXm, hXlim⟩

/-- **FY Theorem 2.12, stationarity + ACVF convolution** (output stationarity and the
double-convolution formula, both *derived* — FY assumes the former and glosses the
latter): `γ_X(k) = Σ'_j Σ'_l φ_j φ_l γ_Y(k + j − l)`. -/
theorem IsFilteredBy.isStationary [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t)) :
    IsStationary X μ ∧
      ∀ k : ℤ, acvf X μ k = ∑' j : ℤ, ∑' l : ℤ, φ j * φ l * acvf Y μ (k + j - l) := by
  sorry

/-- Summability of the output ACVF (derived; FY assumes it): `ℓ¹ ∗ ℓ¹ ∗ ℓ¹`. -/
theorem IsFilteredBy.hasSummableACVF [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hYsum : HasSummableACVF Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t)) :
    HasSummableACVF X μ := by
  sorry

/-- **FY Theorem 2.12 (spectral form)**: `g_X(λ) = |Γ(λ)|² · g_Y(λ)`. -/
theorem IsFilteredBy.spectralDensityOf_eq [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hYsum : HasSummableACVF Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l = ‖transferFun φ l‖ ^ 2 * spectralDensityOf Y μ l := by
  sorry

end StatLean.TimeSeries
