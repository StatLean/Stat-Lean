import StatLean.TimeSeries.Models.WhiteNoise

/-!
# Linear (MA(∞)) processes (FY §2.1.2, eq. (2.1))

The one-sided linear process `X_t = Σ_{j≥0} ψ_j ε_{t−j}` with absolutely summable
coefficients over white noise: well-definedness (`L²` convergence of the partial sums),
existence, stationarity with the autocovariance formula
`γ(k) = σ² Σ_{j≥0} ψ_j ψ_{j+|k|}` (FY eq. (2.2)), strict stationarity under i.i.d.
innovations, and (as an allowed debt in this wave) almost-sure convergence under
independence (FY cites Chow & Teicher 1997, Cor. 3 p. 117).

`IsLinearProcessOf ψ X ε μ` says the partial sums converge to `X t` in `L²`
(`eLpNorm … 2 μ → 0`) at every time — the convergence mode FY works with. (The
*two-sided* linear process of FY Theorem 2.8/2.14 will generalize this in batch B/C.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.2,
eqs. (2.1)–(2.2) (pp. 30–31). (`FY §2.1.2 eq. (2.1)–(2.2)`.)

**Proof formalization notes.** Existence: the partial sums are Cauchy in `L²` by
`ℓ¹ ⊆ ℓ²` of the coefficients and WN orthogonality; completeness of `L²` provides a
limit, chosen measurably per `t`. The ACVF formula interchanges `cov` with the `L²`
limits (continuity of the inner product) and collapses the double series by
uncorrelatedness. Strict stationarity under i.i.d. innovations transports the
finite-dimensional laws of the partial sums (each a fixed measurable function of a
shift of the i.i.d. family) to the a.e./in-measure limit.

**Bibliographic comments.** Infinite moving averages originate with E. Slutsky (1927)
and H. Wold (1938); the `L²` theory is the Wiener–Kolmogorov era's; the almost-sure
convergence of independent series is Kolmogorov's three-series/maximal-inequality circle
(FY cite Y. S. Chow and H. Teicher, *Probability Theory*, 3rd ed., Springer, 1997).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `X` is the **linear process** with coefficients `ψ` over the noise `ε` (FY eq.
(2.1)): at every time the `L²` distance from the partial sums vanishes,
`‖X_t − Σ_{j<N} ψ_j ε_{t−j}‖_{L²(μ)} → 0`. -/
def IsLinearProcessOf (ψ : ℕ → ℝ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N => eLpNorm
      (fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ)
    atTop (𝓝 0)

section Aux

variable {ψ : ℕ → ℝ} {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

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

/-- The `N`-term partial sum `Σ_{j<N} ψ_j ε_{t−j}` of the linear process. -/
private noncomputable def psum (ψ : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω

private lemma memLp_psum (hε : IsWhiteNoise ε σ2 μ) (t : ℤ) (N : ℕ) :
    MemLp (psum ψ ε t N) 2 μ :=
  memLp_finset_sum _ fun j _ => (hε.memLp (t - (j : ℕ))).const_mul (ψ j)

/-- Second moments of white noise: `E[ε_a ε_b] = σ² δ_{ab}` (the means vanish, so the
mixed moment is the covariance). -/
private lemma integral_noise_mul [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (a b : ℤ) : ∫ ω, ε a ω * ε b ω ∂μ = if a = b then σ2 else 0 := by
  have h := covariance_eq_sub (hε.memLp a) (hε.memLp b)
  rw [hε.integral_eq_zero a, zero_mul, sub_zero] at h
  have h2 : μ[ε a * ε b] = ∫ ω, ε a ω * ε b ω ∂μ := by
    simp [Pi.mul_apply]
  rw [h2] at h
  rw [← h]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, covariance_self (hε.memLp a).aestronglyMeasurable.aemeasurable,
      hε.variance_eq a]
  · rw [if_neg hab, hε.uncorrelated a b hab]

/-- The `L²` norm of the noise is `√σ²` at every time. -/
private lemma norm_toLp_noise [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ) (a : ℤ) :
    ‖(hε.memLp a).toLp (ε a)‖ = Real.sqrt σ2 := by
  have h : ‖(hε.memLp a).toLp (ε a)‖ ^ 2 = σ2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp, integral_noise_mul hε a a, if_pos rfl]
  have h2 := Real.sqrt_sq (norm_nonneg ((hε.memLp a).toLp (ε a)))
  rw [h] at h2
  exact h2.symm

/-- The `L²` class of the `N`-term partial sum. -/
private noncomputable def psumLp [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) : Lp ℝ 2 μ :=
  (memLp_psum (ψ := ψ) hε t N).toLp _

private lemma coeFn_psumLp [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) : ⇑(psumLp hε ψ t N) =ᵐ[μ] psum ψ ε t N :=
  (memLp_psum (ψ := ψ) hε t N).coeFn_toLp

/-- Successive partial sums differ by the single term `ψ_N ε_{t−N}`, of `L²` norm
`|ψ_N| √σ²`. -/
private lemma dist_psumLp_succ [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    dist (psumLp hε ψ t N) (psumLp hε ψ t (N + 1)) = |ψ N| * Real.sqrt σ2 := by
  rw [dist_comm, Lp.dist_def]
  have hae : (⇑(psumLp hε ψ t (N + 1)) - ⇑(psumLp hε ψ t N))
      =ᵐ[μ] (ψ N • ε (t - (N : ℕ))) := by
    filter_upwards [coeFn_psumLp hε ψ t (N + 1), coeFn_psumLp hε ψ t N] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2, psum, Finset.sum_range_succ, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, ENNReal.toReal_mul]
  have h : ((eLpNorm (ε (t - (N : ℕ))) 2 μ)).toReal = Real.sqrt σ2 := by
    rw [← Lp.norm_toLp _ (hε.memLp (t - (N : ℕ))), norm_toLp_noise hε]
  rw [h]
  simp

end Aux

/-- **Existence** (FY §2.1.2): over white noise, absolutely summable coefficients define
a linear process (`L²`-limits of the partial sums, chosen measurably). -/
theorem exists_isLinearProcessOf [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: absolutely summable coefficients; FY eq. (2.1)
    (hψ : Summable fun j => |ψ j|)
    -- USER-INPUT: white-noise innovations; FY eq. (2.1)
    (hε : IsWhiteNoise ε σ2 μ) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ IsLinearProcessOf ψ X ε μ := by
  have main : ∀ t : ℤ, ∃ f : Ω → ℝ, Measurable f ∧
      Tendsto (fun N => eLpNorm (fun ω => f ω - psum ψ ε t N ω) 2 μ) atTop (𝓝 0) := by
    intro t
    have hsum : Summable fun N : ℕ => dist (psumLp hε ψ t N) (psumLp hε ψ t N.succ) :=
      (hψ.mul_right (Real.sqrt σ2)).congr fun N => (dist_psumLp_succ hε ψ t N).symm
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
    refine ⟨(Lp.aestronglyMeasurable L).mk _,
      (Lp.aestronglyMeasurable L).stronglyMeasurable_mk.measurable, ?_⟩
    have heq : ∀ N : ℕ,
        eLpNorm (fun ω => ((Lp.aestronglyMeasurable L).mk _) ω - psum ψ ε t N ω) 2 μ
          = edist (psumLp hε ψ t N) L := by
      intro N
      rw [edist_comm, Lp.edist_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(Lp.aestronglyMeasurable L).ae_eq_mk, coeFn_psumLp hε ψ t N] with ω h1 h2
      simp only [Pi.sub_apply, ← h1, h2]
    simp_rw [heq, edist_dist]
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hL)
  choose X hXm hXlim using main
  exact ⟨X, hXm, hXlim⟩

/-- Marginals of a linear process are in `L²`. -/
theorem IsLinearProcessOf.memLp [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    -- LEAN-ONLY: measurability of the limits; supplied by `exists_isLinearProcessOf`
    (hmeas : ∀ t, Measurable (X t)) (t : ℤ) : MemLp (X t) 2 μ := by
  sorry

/-- **Stationarity + the ACVF formula** (FY §2.1.2, eq. (2.2)): a linear process over
white noise is weakly stationary with `γ(k) = σ² Σ_{j≥0} ψ_j ψ_{j+|k|}`. -/
theorem IsLinearProcessOf.isStationary [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) :
    IsStationary X μ ∧
      ∀ k : ℤ, acvf X μ k = σ2 * ∑' j : ℕ, ψ j * ψ (j + k.natAbs) := by
  sorry

/-- **Strict stationarity under i.i.d. innovations** (FY §2.1.2, asserted): a linear
process over i.i.d. noise is strictly stationary. -/
theorem IsLinearProcessOf.isStrictlyStationary [IsProbabilityMeasure μ] {ψ : ℕ → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsIIDNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) :
    IsStrictlyStationary X μ := by
  sorry

/-- **Almost-sure convergence under independence** — ALLOWED DEBT in wave A2 (FY cites
Chow & Teicher 1997, Cor. 3 p. 117; route: Kolmogorov maximal inequality / martingale
convergence on the partial sums). -/
theorem IsLinearProcessOf.ae_tendsto [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsIIDNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) atTop (𝓝 (X t ω)) := by
  sorry

end StatLean.TimeSeries
