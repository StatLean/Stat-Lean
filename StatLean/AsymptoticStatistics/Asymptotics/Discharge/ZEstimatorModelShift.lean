import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasResidualExplicit
import StatLean.AsymptoticStatistics.Core.QMDPath
import StatLean.AsymptoticStatistics.ForMathlib.MatrixInProbability

/-!
# QMD transport of a random score under a moving model

QMD infrastructure for the model-shift term in vdV (25.52) and
Theorem 25.59.  The scalar statements expose the sign before any information
inverse is applied:

`√n (P scoreHat - P_{thetaHat,eta} scoreHat)
  + √n (thetaHat-theta0) <score0, path.score> = o_P(1)`.

Consequently the Z-estimating-equation algebra produces the covariant
`+ I^{-1} B_n` correction.  The literal `+ B_n` display in vdV is recovered
only in information-normalized coordinates (`I = 1`).

The native finite-dimensional statements use one QMD model, one cross-moment
matrix, and one continuous linear map.  They do not invert coordinates
separately.

Reference: vdV §25.8, equation (25.52), pp. 391--392, and Theorem 25.59,
p. 395 after information normalization.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Matrix.Norms.L2Operator

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Extend a punctured limit by the prescribed value at zero. -/
private lemma tendsto_zeroExtension {E F : Type*}
    [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]
    (f extension : E → F) (hf : Tendsto f (𝓝[≠] 0) (𝓝 0))
    (hzero : extension 0 = 0) (hne : ∀ x ≠ 0, extension x = f x) :
    Tendsto extension (𝓝 0) (𝓝 0) := by
  classical
  intro s hs
  change extension ⁻¹' s ∈ 𝓝 0
  obtain ⟨t, ht, hts⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hf hs)
  refine mem_of_superset ht fun x hx => ?_
  by_cases h0 : x = 0
  · simpa [h0, hzero] using mem_of_mem_nhds hs
  · simpa [hne x h0] using hts ⟨hx, h0⟩

/-- Continuous-at-zero maps preserve the project's varying-base convergence in probability. -/
private lemma tendstoInProbZero_comp_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → E} {f : E → F}
    (hZ : TendstoInProbZero P Z) (hf : Tendsto f (𝓝 0) (𝓝 0)) :
    TendstoInProbZero P (fun n omega => f (Z n omega)) := by
  intro epsilon hepsilon
  have hev : {x | dist (f x) 0 < epsilon} ∈ 𝓝 (0 : E) :=
    Metric.tendsto_nhds.mp hf epsilon hepsilon
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hsub : ∀ n, {omega | epsilon ≤ ‖f (Z n omega)‖} ⊆
      {omega | delta ≤ ‖Z n omega‖} := by
    intro n omega homega
    by_contra hnot
    have hsmall := hball (by simpa [Metric.mem_ball, dist_zero_right] using not_le.mp hnot)
    simp only [Set.mem_setOf_eq, dist_zero_right] at hsmall homega
    exact (not_lt_of_ge homega) hsmall
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hZ delta hdelta) (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono (hsub n))

/-- Local `o_P(1)` additivity, kept here because the existing project proof is private
to an unrelated assembly module. -/
private lemma tendstoInProbZero_add
    {G : Type*} [NormedAddCommGroup G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z W : ∀ n, Omega' n → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun n omega => Z n omega + W n omega) := by
  intro epsilon hepsilon
  have hsub : ∀ n, {omega | epsilon ≤ ‖Z n omega + W n omega‖} ⊆
      {omega | epsilon / 2 ≤ ‖Z n omega‖} ∪
        {omega | epsilon / 2 ≤ ‖W n omega‖} := by
    intro n omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
    simp only [Set.mem_setOf_eq] at homega
    exact (not_lt_of_ge homega) <|
      lt_of_le_of_lt (norm_add_le (Z n omega) (W n omega)) (by linarith)
  have hsum := (hZ (epsilon / 2) (half_pos hepsilon)).add
    (hW (epsilon / 2) (half_pos hepsilon))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hsum)
    (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n =>
      (measureReal_mono (hsub n)).trans (measureReal_union_le _ _))

/-- Pointwise norm domination preserves varying-base convergence in probability. -/
private lemma tendstoInProbZero_mono
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, Omega' n → G} {W : ∀ n, Omega' n → H}
    (hle : ∀ n omega, ‖Z n omega‖ ≤ ‖W n omega‖)
    (hW : TendstoInProbZero P W) : TendstoInProbZero P Z := by
  intro epsilon hepsilon
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hW epsilon hepsilon) (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono fun _ homega => homega.trans (hle _ _))

/-- A deterministic scalar multiple of an `o_P(1)` family is `o_P(1)`. -/
private lemma tendstoInProbZero_const_smul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Omega' : ℕ → Type*} [∀ n, MeasurableSpace (Omega' n)]
    {P : ∀ n, Measure (Omega' n)} {Z : ∀ n, Omega' n → G}
    (c : ℝ) (hZ : TendstoInProbZero P Z) :
    TendstoInProbZero P (fun n omega => c • Z n omega) := by
  intro epsilon hepsilon
  rcases eq_or_ne c 0 with rfl | hc
  · have hset : ∀ n, {omega | epsilon ≤ ‖(0 : ℝ) • Z n omega‖} =
        (∅ : Set (Omega' n)) := by
      intro n
      ext omega
      simp [not_le.mpr hepsilon]
    simp only [hset, measureReal_empty]
    exact tendsto_const_nhds
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    simpa only [norm_smul, Real.norm_eq_abs, div_le_iff₀ hcpos, mul_comm] using
      hZ (epsilon / |c|) (div_pos hepsilon hcpos)

/-- Pull an `L²(P)` function back to the common dominator using `sqrt (dP/dmu)`. -/
private lemma memLp_sqrt_rnDeriv_smul_of_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P mu : Measure Omega} [IsFiniteMeasure P] [SigmaFinite mu]
    (hPmu : P ≪ mu) {f : Omega → E} (hf : MemLp f 2 P) :
    MemLp (fun omega => Real.sqrt ((P.rnDeriv mu omega).toReal) • f omega) 2 mu := by
  have hP : P = mu.withDensity (P.rnDeriv mu) :=
    (Measure.withDensity_rnDeriv_eq P mu hPmu).symm
  let F : Lp E 2 P := hf.toLp f
  have hF_eq : (F : Omega → E) =ᵐ[P] f := MemLp.coeFn_toLp hf
  have hF_eq_density : (F : Omega → E) =ᵐ[mu.withDensity (P.rnDeriv mu)] f := by
    have hae : ae (mu.withDensity (P.rnDeriv mu)) = ae P := congrArg ae hP.symm
    rw [hae]
    exact hF_eq
  have hF_eq_mu :=
    (ae_withDensity_iff (Measure.measurable_rnDeriv P mu)).mp hF_eq_density
  have hweighted_meas : AEStronglyMeasurable
      (fun omega => Real.sqrt ((P.rnDeriv mu omega).toReal) • f omega) mu := by
    have hF_meas : StronglyMeasurable (F : Omega → E) := Lp.stronglyMeasurable F
    have hmeas : AEStronglyMeasurable
        (fun omega => Real.sqrt ((P.rnDeriv mu omega).toReal) • (F : Omega → E) omega) mu :=
      ((Measure.measurable_rnDeriv P mu).ennreal_toReal.sqrt.aestronglyMeasurable).smul
        hF_meas.aestronglyMeasurable
    refine hmeas.congr ?_
    filter_upwards [hF_eq_mu] with omega homega
    by_cases hrn : P.rnDeriv mu omega = 0
    · simp [hrn]
    · rw [homega hrn]
  have hi : Integrable (fun omega => ‖f omega‖ ^ 2 * (P.rnDeriv mu omega).toReal) mu := by
    rw [← MeasureTheory.integrable_withDensity_iff
      (Measure.measurable_rnDeriv P mu) (Measure.rnDeriv_lt_top P mu), ← hP]
    exact hf.integrable_norm_pow (by norm_num)
  rw [memLp_two_iff_integrable_sq_norm hweighted_meas]
  convert hi using 1
  funext omega
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ENNReal.toReal_nonneg]
  ring

/-- Bochner-valued L2 Cauchy--Schwarz, in the exact square-integral form used below. -/
private lemma norm_integral_smul_le_sqrt_integral_sq
    {d : ℕ} {mu : Measure Omega} {f : Omega → ℝ}
    {g : Omega → EuclideanSpace ℝ (Fin d)}
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    ‖∫ omega, f omega • g omega ∂mu‖ ≤
      Real.sqrt (∫ omega, f omega ^ 2 ∂mu) *
        Real.sqrt (∫ omega, ‖g omega‖ ^ 2 ∂mu) := by
  calc
    _ ≤ ∫ omega, ‖f omega • g omega‖ ∂mu := norm_integral_le_integral_norm _
    _ = ∫ omega, |f omega| * ‖g omega‖ ∂mu := by
      apply integral_congr_ae
      exact Eventually.of_forall fun omega => by
        change ‖f omega • g omega‖ = |f omega| * ‖g omega‖
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |∫ omega, |f omega| * ‖g omega‖ ∂mu| := le_abs_self _
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
          mu hf.norm hg.norm

/-- The pointwise square-root-density transport identity. -/
private lemma scalar_sqrt_transport_identity (a b z e c ell : ℝ) :
    z * a ^ 2 - z * b ^ 2 - e * (c * ell * b ^ 2) =
      z * (a + b) * (a - b - e / 2 * ell * b) +
        e / 2 * ((z * (a + b) - 2 * c * b) * (ell * b)) := by
  ring

/-- Vector version of the same square-root-density transport identity. -/
private lemma vector_sqrt_transport_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b ell : ℝ) (z v : E) :
    a ^ 2 • z - b ^ 2 • z - (ell * b ^ 2) • v =
      (a - b - (1 / 2 : ℝ) * ell * b) • ((a + b) • z) +
        (1 / 2 : ℝ) • ((ell * b) • ((a + b) • z - (2 * b) • v)) := by
  module

/-- The raw moving-model bias from vdV (25.52):
`sqrt n * P_{thetaHat,eta} scoreHat`.

The path parameter is the estimator displacement from `theta0`; hence the
nuisance component of the integrating law is fixed at truth.  At `n = 0`,
`Real.sqrt 0 = 0`, so the definition is zero regardless of the integral. -/
noncomputable def rawMovingBias
    {P : Measure Omega} [IsProbabilityMeasure P] (gamma : QMDPath P)
    (estimator : ∀ n, (Fin n → Omega) → ℝ) (theta0 : ℝ)
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ)
    (n : ℕ) (X : Fin n → Omega) : ℝ :=
  Real.sqrt n * ∫ omega, scoreHat n X omega
    ∂(gamma.curve (estimator n X - theta0))

/-- Analytic hypotheses for transporting a random scalar score along a
dominated QMD path.

The bundle contains only integrability, consistency, and the three robust
Hellinger-weighted L2 conditions (membership, tightness, and transport).  In
particular, it contains neither an integral-shift expansion nor an
asymptotic-linearity conclusion. -/
structure HellingerScoreTransportHyp
    (P : Measure Omega) [IsProbabilityMeasure P]
    (gamma : QMDPath P)
    (estimator : ∀ n, (Fin n → Omega) → ℝ) (theta0 : ℝ)
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ)
    (score0 : Omega → ℝ) : Prop where
  /-- the random score is integrable under the true law. -/
  scoreHat_integrable_truth : ∀ n X, Integrable (scoreHat n X) P
  /-- the random score is integrable under the moving law. -/
  scoreHat_integrable_moving : ∀ n X,
    Integrable (scoreHat n X) (gamma.curve (estimator n X - theta0))
  /-- the limiting score belongs to L2 of the true law. -/
  score0_memLp : MemLp score0 2 P
  /-- the Hellinger-weighted random score is genuinely in
  `L2(gamma.dominating)`.  This prevents the Bochner-integral convention for
  non-integrable functions from making the transport condition vacuous. -/
  weightedScore_memLp : ∀ n X, MemLp (fun omega =>
    scoreHat n X omega *
      (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
          gamma.dominating omega).toReal)
        + Real.sqrt (((gamma.curve 0).rnDeriv
            gamma.dominating omega).toReal))) 2 gamma.dominating
  /-- the L2 norms of the Hellinger-weighted random scores are
  bounded in probability.  This is the `O_P(1)` factor paired with the
  normalized QMD square-root-density remainder. -/
  weightedScore_tight : IsBoundedInProb
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      |scoreHat n X omega *
        (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
            gamma.dominating omega).toReal)
          + Real.sqrt (((gamma.curve 0).rnDeriv
              gamma.dominating omega).toReal))| ^ 2
      ∂gamma.dominating))
  /-- Hellinger-weighted L2 transport of the random score.
  The expression is the genuine square-root-density tangent transport
  `scoreHat * (sqrt p_delta + sqrt p_0) - 2 * score0 * sqrt p_0`.
  This is an analytic norm condition, not the desired integral-shift result. -/
  weightedScore_transport : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      Real.sqrt (∫ omega,
        |scoreHat n X omega *
            (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
              gamma.dominating omega).toReal)
              + Real.sqrt (((gamma.curve 0).rnDeriv
                  gamma.dominating omega).toReal))
          - 2 * score0 omega *
              Real.sqrt (((gamma.curve 0).rnDeriv
                gamma.dominating omega).toReal)| ^ 2
        ∂gamma.dominating))
  /-- consistency of the estimator along the QMD path. -/
  consistency : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => estimator n X - theta0)

set_option maxHeartbeats 1200000 in
-- The RN/Bochner normalization proof elaborates several large dependent integrals.
/-- QMD model shift normalized by the nonzero parameter displacement.

This is the rate-free transport statement: consistency selects the local QMD
regime.  The value at zero is set explicitly to zero, avoiding a false demand
that an arbitrary `0/0` representation converge.

Proof idea: `h.consistency` localizes the punctured-neighborhood QMD limit;
`weightedScore_memLp` excludes Bochner fallback; `weightedScore_tight` pairs
with the normalized QMD remainder; and `weightedScore_transport` identifies
the limiting cross moment. -/
theorem qmdPath_modelShift_normalized_oP
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : ∀ n, (Fin n → Omega) → ℝ} {theta0 : ℝ}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ}
    {score0 : Omega → ℝ}
    (h : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat score0) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        if delta = 0 then 0 else
          (((∫ omega, scoreHat n X omega ∂(gamma.curve delta)) -
              ∫ omega, scoreHat n X omega ∂P)
            - delta *
                ∫ omega, score0 omega * (gamma.score : Omega → ℝ) omega ∂P)
            / |delta|) := by
  let s : ℝ → Omega → ℝ := fun delta omega =>
    Real.sqrt (((gamma.curve delta).rnDeriv gamma.dominating omega).toReal)
  let g : Omega → ℝ := gamma.score
  let r : ℝ → Omega → ℝ := fun delta omega =>
    s delta omega - s 0 omega - (delta / 2) * g omega * s 0 omega
  let W : ∀ n, (Fin n → Omega) → Omega → ℝ := fun n X omega =>
    scoreHat n X omega * (s (estimator n X - theta0) omega + s 0 omega)
  let K : ∀ n, (Fin n → Omega) → Omega → ℝ := fun n X omega =>
    W n X omega - 2 * score0 omega * s 0 omega
  let K0 : Omega → ℝ := fun omega => g omega * s 0 omega
  have hs : ∀ delta, MemLp (s delta) 2 gamma.dominating := by
    intro delta
    letI := gamma.curve_isProbability delta
    exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
      (gamma.curve_absContinuous delta)
  have hPac : P ≪ gamma.dominating := by
    simpa only [gamma.curve_at_zero] using gamma.curve_absContinuous 0
  have hscore0s0 : MemLp (fun omega => s 0 omega * score0 omega) 2 gamma.dominating := by
    rw [show s 0 = fun omega =>
      Real.sqrt ((P.rnDeriv gamma.dominating omega).toReal) from by
        funext omega; simp [s, gamma.curve_at_zero]]
    exact memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := gamma.dominating)
      hPac h.score0_memLp
  have hgP : MemLp g 2 P := by
    simpa [g] using Lp.memLp (gamma.score : Lp ℝ 2 P)
  have hK0 : MemLp K0 2 gamma.dominating := by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := gamma.dominating) hPac hgP
    simpa [K0, s, g, gamma.curve_at_zero, mul_comm] using hm
  have hr : ∀ delta, MemLp (r delta) 2 gamma.dominating := fun delta => by
    simpa [r, K0, mul_assoc] using
      ((hs delta).sub (hs 0)).sub (hK0.const_mul (delta / 2))
  let qraw : ℝ → ℝ := fun delta =>
    Real.sqrt (∫ omega, r delta omega ^ 2 ∂gamma.dominating) / |delta|
  let q : ℝ → ℝ := fun delta => if delta = 0 then 0 else qraw delta
  have hqraw : Tendsto qraw (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
      gamma.qmd_limit
    simp only [Function.comp_def, ENNReal.toReal_zero] at ht
    refine ht.congr' (Eventually.of_forall fun delta => ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (abs_nonneg delta),
      ← AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
        (hr delta)]
  have hq : Tendsto q (𝓝 (0 : ℝ)) (𝓝 0) :=
    tendsto_zeroExtension qraw q hqraw (by simp [q]) (by intro x hx; simp [q, hx])
  have hq_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => q (estimator n X - theta0)) :=
    tendstoInProbZero_comp_zero h.consistency hq
  have hW_tight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, W n X omega ^ 2 ∂gamma.dominating)) := by
    simpa only [W, s, sq_abs] using h.weightedScore_tight
  have hterm1 := tendstoInProbZero_of_isBoundedInProb_mul hW_tight hq_prob
  have hK_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, K n X omega ^ 2 ∂gamma.dominating)) := by
    simpa only [K, W, s, sq_abs] using h.weightedScore_transport
  have hterm2 := tendstoInProbZero_const_smul
    (Real.sqrt (∫ omega, K0 omega ^ 2 ∂gamma.dominating) / 2) hK_prob
  have henv := tendstoInProbZero_add hterm1 hterm2
  refine tendstoInProbZero_mono (fun n X => ?_) henv
  simp only [q, qraw, smul_eq_mul]
  by_cases hdelta : estimator n X - theta0 = 0
  · simp only [hdelta, ↓reduceIte, norm_zero, mul_zero, zero_add]
    exact norm_nonneg _
  · simp only [hdelta, ↓reduceIte]
    have hWmem : MemLp (W n X) 2 gamma.dominating := h.weightedScore_memLp n X
    have hKmem : MemLp (K n X) 2 gamma.dominating := by
      have hm : MemLp (fun omega => 2 * score0 omega * s 0 omega) 2
          gamma.dominating := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscore0s0.const_mul 2
      exact hWmem.sub hm
    have hshift :
        ((∫ omega, scoreHat n X omega ∂(gamma.curve (estimator n X - theta0))) -
            ∫ omega, scoreHat n X omega ∂P) -
          (estimator n X - theta0) * ∫ omega, score0 omega * g omega ∂P =
        ∫ omega, W n X omega * r (estimator n X - theta0) omega ∂gamma.dominating +
          ((estimator n X - theta0) / 2) *
            ∫ omega, K n X omega * K0 omega ∂gamma.dominating := by
      letI := gamma.curve_isProbability (estimator n X - theta0)
      have hi_delta := (integrable_toReal_rnDeriv_mul_iff
        (gamma.curve_absContinuous (estimator n X - theta0))).2
          (h.scoreHat_integrable_moving n X)
      have hi_zero := (integrable_toReal_rnDeriv_mul_iff hPac).2
        (h.scoreHat_integrable_truth n X)
      have hi_cross : Integrable (fun omega => score0 omega * g omega) P :=
        h.score0_memLp.integrable_mul hgP
      have hi_cross_mu := (integrable_toReal_rnDeriv_mul_iff hPac).2
        (by simpa [mul_comm] using hi_cross)
      rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          (gamma.curve_absContinuous (estimator n X - theta0)) (scoreHat n X),
        AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          hPac (scoreHat n X),
        AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          hPac (fun omega => score0 omega * g omega),
        ← integral_sub (by simpa [s, mul_comm, Real.sq_sqrt ENNReal.toReal_nonneg] using hi_delta)
          (by simpa [s, mul_comm, Real.sq_sqrt ENNReal.toReal_nonneg] using hi_zero),
        ← integral_const_mul,
        ← integral_sub,
        ← integral_const_mul,
        ← integral_add]
      · refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
        simp only [W, K, K0, r, s]
        rw [gamma.curve_at_zero]
        have hd := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ ((gamma.curve (estimator n X - theta0)).rnDeriv
            gamma.dominating omega).toReal)
        have h0 := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ (P.rnDeriv gamma.dominating omega).toReal)
        simpa only [hd, h0] using scalar_sqrt_transport_identity
          (Real.sqrt (((gamma.curve (estimator n X - theta0)).rnDeriv
            gamma.dominating omega).toReal))
          (Real.sqrt ((P.rnDeriv gamma.dominating omega).toReal))
          (scoreHat n X omega) (estimator n X - theta0) (score0 omega) (g omega)
      · exact hWmem.integrable_mul (hr _)
      · exact (hKmem.integrable_mul hK0).const_mul _
      · simpa [Pi.sub_apply, mul_comm] using hi_delta.sub hi_zero
      · simpa [mul_assoc, mul_comm, mul_left_comm] using hi_cross_mu.const_mul
          (estimator n X - theta0)
    rw [hshift]
    have hcs1 := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      gamma.dominating hWmem (hr (estimator n X - theta0))
    have hcs2 := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      gamma.dominating hKmem hK0
    simp only [Real.norm_eq_abs]
    rw [abs_div]
    simp only [abs_abs]
    have henv_nonneg : 0 ≤
        Real.sqrt (∫ omega, W n X omega ^ 2 ∂gamma.dominating) *
            (Real.sqrt (∫ omega, r (estimator n X - theta0) omega ^ 2
              ∂gamma.dominating) / |estimator n X - theta0|) +
          Real.sqrt (∫ omega, K0 omega ^ 2 ∂gamma.dominating) / 2 *
            Real.sqrt (∫ omega, K n X omega ^ 2 ∂gamma.dominating) := by positivity
    rw [abs_of_nonneg henv_nonneg]
    calc
      _ ≤ (|∫ omega, W n X omega * r (estimator n X - theta0) omega
                ∂gamma.dominating| +
            |(estimator n X - theta0) / 2| *
              |∫ omega, K n X omega * K0 omega ∂gamma.dominating|) /
            |estimator n X - theta0| := by
        apply div_le_div_of_nonneg_right _ (abs_nonneg _)
        simpa only [abs_mul] using abs_add_le
          (∫ omega, W n X omega * r (estimator n X - theta0) omega
            ∂gamma.dominating)
          (((estimator n X - theta0) / 2) *
            ∫ omega, K n X omega * K0 omega ∂gamma.dominating)
      _ ≤ (Real.sqrt (∫ omega, W n X omega ^ 2 ∂gamma.dominating) *
              Real.sqrt (∫ omega, r (estimator n X - theta0) omega ^ 2
                ∂gamma.dominating) +
            (|estimator n X - theta0| / 2) *
              (Real.sqrt (∫ omega, K n X omega ^ 2 ∂gamma.dominating) *
                Real.sqrt (∫ omega, K0 omega ^ 2 ∂gamma.dominating))) /
            |estimator n X - theta0| := by
        apply div_le_div_of_nonneg_right _ (abs_nonneg _)
        apply add_le_add hcs1
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left hcs2 (by positivity)
      _ = _ := by field_simp [abs_ne_zero.mpr hdelta]

/-- The ordinary scalar model-shift expansion from root-`n` tightness.

The displayed sign is deliberately `P scoreHat - P_{thetaHat,eta} scoreHat`
plus the QMD cross moment.  Thus solving the estimating equation yields the
corrected `+ I^{-1} B_n` term.

Proof idea: apply `qmdPath_modelShift_normalized_oP`; `hTight` controls
`sqrt n * |delta|`, while the shared bundle's consistency is the independent
localization input needed by the normalized theorem. -/
theorem qmdPath_modelShift_oP_of_sqrtN_tight
    {P : Measure Omega} [IsProbabilityMeasure P]
    {gamma : QMDPath P}
    {estimator : ∀ n, (Fin n → Omega) → ℝ} {theta0 : ℝ}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → ℝ}
    {score0 : Omega → ℝ}
    (h : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat score0)
    -- the local parameter `sqrt n (thetaHat-theta0)` is `O_P(1)`.
    (hTight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * (estimator n X - theta0))) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        Real.sqrt n *
            ((∫ omega, scoreHat n X omega ∂P) -
              ∫ omega, scoreHat n X omega
                ∂(gamma.curve (estimator n X - theta0)))
          + Real.sqrt n * (estimator n X - theta0) *
              ∫ omega, score0 omega * (gamma.score : Omega → ℝ) omega ∂P) := by
  have hnorm := qmdPath_modelShift_normalized_oP h
  have hscale : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * |estimator n X - theta0|) := by
    simpa only [IsBoundedInProb, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hTight
  have hprod := tendstoInProbZero_of_isBoundedInProb_mul hscale hnorm
  have hneg := tendstoInProbZero_const_smul (-1) hprod
  convert hneg using 1
  funext n X
  let delta := estimator n X - theta0
  by_cases hdelta : delta = 0
  · simp [delta, hdelta, gamma.curve_at_zero]
  · simp only [delta, hdelta, ↓reduceIte, smul_eq_mul]
    have habs : |estimator n X - theta0| ≠ 0 := by
      simpa [delta] using abs_ne_zero.mpr hdelta
    field_simp [habs]
    ring

/-! ## Genuine native finite-dimensional interface -/

/-- A dominated QMD model with a native Euclidean parameter and score.

This is not a family of scalar paths: its QMD remainder is stated once for an
arbitrary vector displacement and uses the single linear form
`h |-> <h, score>`. -/
structure QMDModel (P : Measure Omega) [IsProbabilityMeasure P] (d : ℕ) where
  /-- Constitutive (vdV §7.2 and §25.3): the local parameter curve of laws. -/
  curve : EuclideanSpace ℝ (Fin d) → Measure Omega
  /-- Constitutive (vdV §7.2): the model passes through truth at zero. -/
  curve_at_zero : curve 0 = P
  /-- Constitutive (vdV §7.2): every member of the local model is a probability law. -/
  curve_isProbability : ∀ h, IsProbabilityMeasure (curve h)
  /-- Constitutive (dominated specialization of vdV §7.2): one common dominating measure. -/
  dominating : Measure Omega
  /-- Constitutive (dominated specialization): every local law is dominated. -/
  curve_absContinuous : ∀ h, curve h ≪ dominating
  /-- Mathlib's Radon--Nikodym API requires sigma-finiteness. -/
  dominating_sigmaFinite : SigmaFinite dominating
  /-- Constitutive (vdV §7.2): the native vector score. -/
  score : Omega → EuclideanSpace ℝ (Fin d)
  /-- measurable representative for the native score. -/
  score_measurable : Measurable score
  /-- Constitutive (vdV Lemma 7.6): the score is square-integrable. -/
  score_memLp : MemLp score 2 P
  /-- Constitutive (vdV Lemma 7.6): the score has mean zero. -/
  score_mean_zero : ∫ omega, score omega ∂P = 0
  /-- Constitutive (vdV §7.2, equation (7.2)): native square-root-density
  remainder, with one Euclidean linear form and no coordinatewise paths. -/
  qmd_limit : Tendsto
    (fun h : EuclideanSpace ℝ (Fin d) =>
      eLpNorm (fun omega : Omega =>
        Real.sqrt (((curve h).rnDeriv dominating omega).toReal)
          - Real.sqrt (((curve 0).rnDeriv dominating omega).toReal)
          - (1 / 2 : ℝ) * ⟪h, score omega⟫_ℝ *
              Real.sqrt (((curve 0).rnDeriv dominating omega).toReal))
        2 dominating / ENNReal.ofReal ‖h‖)
      (nhdsWithin 0 {0}ᶜ) (𝓝 (0 : ℝ≥0∞))

instance {P : Measure Omega} [IsProbabilityMeasure P] {d : ℕ}
    (M : QMDModel P d) : SigmaFinite M.dominating := M.dominating_sigmaFinite

/-- Native raw moving bias `sqrt n * P_{thetaHat,eta} scoreHat`.

At dimension zero this is the unique vector in the zero-dimensional Euclidean
space; at `n = 0` it is also killed by the scalar factor `Real.sqrt 0`. -/
noncomputable def rawMovingBias_vec {d : ℕ} {P : Measure Omega}
    [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d))
    (theta0 : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Omega) : EuclideanSpace ℝ (Fin d) :=
  Real.sqrt n • ∫ omega, scoreHat n X omega
    ∂(M.curve (estimator n X - theta0))

/-- Native cross moment between a vector estimating score and the QMD score.

Entry `(j,k)` is `P[score0_j * qmdScore_k]`; its action is always taken through
the single map `Matrix.toEuclideanCLM`, including when `d = 1`. -/
noncomputable def qmdCrossMoment {d : ℕ} (P : Measure Omega)
    [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (score0 : Omega → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∫ omega, score0 omega j * M.score omega k ∂P

/-- The cross-moment matrix acts as the integral of the score rank-one action. -/
private lemma qmdCrossMoment_apply {d : ℕ} {P : Measure Omega}
    [IsProbabilityMeasure P] (M : QMDModel (Omega := Omega) P d)
    (score0 : Omega → EuclideanSpace ℝ (Fin d))
    (hscore0 : MemLp score0 2 P)
    (delta : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (qmdCrossMoment P M score0) delta =
      ∫ omega, ⟪delta, M.score omega⟫_ℝ • score0 omega ∂P := by
  have hinner : MemLp (fun omega => ⟪delta, M.score omega⟫_ℝ) 2 P :=
    M.score_memLp.const_inner delta
  have hint : Integrable (fun omega => ⟪delta, M.score omega⟫_ℝ • score0 omega) P :=
    ((hscore0.smul hinner : MemLp _ 1 P).integrable (by norm_num))
  ext j
  change ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
      (qmdCrossMoment P M score0)) delta).ofLp j =
    (EuclideanSpace.proj j) (∫ omega, ⟪delta, M.score omega⟫_ℝ • score0 omega ∂P)
  rw [← (EuclideanSpace.proj j).integral_comp_comm hint]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    qmdCrossMoment, PiLp.inner_apply, EuclideanSpace.coe_proj,
    PiLp.smul_apply, smul_eq_mul]
  have heq :
      (fun x => (∑ i, ⟪delta.ofLp i, (M.score x).ofLp i⟫_ℝ) *
        (score0 x).ofLp j) =
        fun x => ∑ i, delta.ofLp i *
          ((score0 x).ofLp j * (M.score x).ofLp i) := by
    funext x
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp only [conj_trivial]
    change (M.score x).ofLp i * delta.ofLp i * (score0 x).ofLp j =
      delta.ofLp i * ((score0 x).ofLp j * (M.score x).ofLp i)
    ring
  rw [heq]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi
    have h0j := hscore0.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
    have hgi := M.score_memLp.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
    exact (h0j.integrable_mul hgi).const_mul _

set_option maxHeartbeats 1200000 in
-- This deterministic estimate is separated from the probabilistic localization
-- so that Lean elaborates the two analytic layers independently.
private lemma native_modelShift_normalized_bound
    {d : ℕ} {μ : Measure Omega}
    {delta : EuclideanSpace ℝ (Fin d)} (hdelta : delta ≠ 0)
    {r f G : Omega → ℝ}
    {W K : Omega → EuclideanSpace ℝ (Fin d)}
    (hr : MemLp r 2 μ) (hf : MemLp f 2 μ) (hG : MemLp G 2 μ)
    (hW : MemLp W 2 μ) (hK : MemLp K 2 μ)
    (hpoint : ∀ omega, f omega ^ 2 ≤ ‖delta‖ ^ 2 * G omega ^ 2) :
    ‖delta‖⁻¹ * ‖(∫ omega, r omega • W omega ∂μ) +
          (1 / 2 : ℝ) • ∫ omega, f omega • K omega ∂μ‖ ≤
      Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) *
          (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) / ‖delta‖) +
        Real.sqrt (∫ omega, G omega ^ 2 ∂μ) / 2 *
          Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ) := by
  have hcs1 := norm_integral_smul_le_sqrt_integral_sq hr hW
  have hcs2 := norm_integral_smul_le_sqrt_integral_sq hf hK
  have hint :
      ∫ omega, f omega ^ 2 ∂μ ≤
        ‖delta‖ ^ 2 * ∫ omega, G omega ^ 2 ∂μ := by
    calc
      _ ≤ ∫ omega, ‖delta‖ ^ 2 * G omega ^ 2 ∂μ :=
        integral_mono hf.integrable_sq
          (hG.integrable_sq.const_mul (‖delta‖ ^ 2)) hpoint
      _ = _ := by rw [integral_const_mul]
  have hsqrt :
      Real.sqrt (∫ omega, f omega ^ 2 ∂μ) ≤
        ‖delta‖ * Real.sqrt (∫ omega, G omega ^ 2 ∂μ) := by
    have hs := Real.sqrt_le_sqrt hint
    rw [Real.sqrt_mul (sq_nonneg ‖delta‖), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg delta)] at hs
    exact hs
  have hnorm_ne : ‖delta‖ ≠ 0 := norm_ne_zero_iff.mpr hdelta
  have hfactor :
      ‖delta‖⁻¹ * Real.sqrt (∫ omega, f omega ^ 2 ∂μ) ≤
        Real.sqrt (∫ omega, G omega ^ 2 ∂μ) := by
    calc
      _ ≤ ‖delta‖⁻¹ *
          (‖delta‖ * Real.sqrt (∫ omega, G omega ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hsqrt (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by field_simp [hnorm_ne]
  have htri :
      ‖(∫ omega, r omega • W omega ∂μ) +
            (1 / 2 : ℝ) • ∫ omega, f omega • K omega ∂μ‖ ≤
        ‖∫ omega, r omega • W omega ∂μ‖ +
          (1 / 2 : ℝ) * ‖∫ omega, f omega • K omega ∂μ‖ := by
    calc
      _ ≤ ‖∫ omega, r omega • W omega ∂μ‖ +
          ‖(1 / 2 : ℝ) • ∫ omega, f omega • K omega ∂μ‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      ‖∫ omega, r omega • W omega ∂μ‖ +
            (1 / 2 : ℝ) * ‖∫ omega, f omega • K omega ∂μ‖ ≤
        Real.sqrt (∫ omega, r omega ^ 2 ∂μ) *
              Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) +
          (1 / 2 : ℝ) * (Real.sqrt (∫ omega, f omega ^ 2 ∂μ) *
            Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ)) :=
    add_le_add hcs1 (mul_le_mul_of_nonneg_left hcs2 (by norm_num))
  calc
    _ ≤ ‖delta‖⁻¹ *
        (‖∫ omega, r omega • W omega ∂μ‖ +
          (1 / 2 : ℝ) * ‖∫ omega, f omega • K omega ∂μ‖) :=
      mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr (norm_nonneg delta))
    _ ≤ ‖delta‖⁻¹ *
        (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) *
            Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) +
          (1 / 2 : ℝ) * (Real.sqrt (∫ omega, f omega ^ 2 ∂μ) *
            Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ))) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (norm_nonneg delta))
    _ = Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) *
          (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) / ‖delta‖) +
        (1 / 2 : ℝ) * Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ) *
          (‖delta‖⁻¹ * Real.sqrt (∫ omega, f omega ^ 2 ∂μ)) := by
      field_simp [hnorm_ne]
    _ ≤ Real.sqrt (∫ omega, ‖W omega‖ ^ 2 ∂μ) *
          (Real.sqrt (∫ omega, r omega ^ 2 ∂μ) / ‖delta‖) +
        (1 / 2 : ℝ) * Real.sqrt (∫ omega, ‖K omega‖ ^ 2 ∂μ) *
          Real.sqrt (∫ omega, G omega ^ 2 ∂μ) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.sqrt_nonneg _)))
    _ = _ := by ring

/-- Native analogue of `HellingerScoreTransportHyp`, with the same
membership/tightness/transport split and no integral-shift conclusion. -/
structure HellingerScoreTransportHypVec
    {d : ℕ} (P : Measure Omega) [IsProbabilityMeasure P]
    (M : QMDModel (Omega := Omega) P d)
    (estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d))
    (theta0 : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d))
    (score0 : Omega → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- integrability under the true law. -/
  scoreHat_integrable_truth : ∀ n X, Integrable (scoreHat n X) P
  /-- integrability under the moving law. -/
  scoreHat_integrable_moving : ∀ n X,
    Integrable (scoreHat n X) (M.curve (estimator n X - theta0))
  /-- the limiting vector score belongs to L2 of truth. -/
  score0_memLp : MemLp score0 2 P
  /-- the native Hellinger-weighted random score genuinely belongs
  to `L2(M.dominating)`, excluding the non-integrable Bochner fallback. -/
  weightedScore_memLp : ∀ n X, MemLp (fun omega =>
    (Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
        M.dominating omega).toReal)
      + Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
        scoreHat n X omega) 2 M.dominating
  /-- the native weighted-score L2 norms are `O_P(1)`, to pair
  with the single native QMD remainder. -/
  weightedScore_tight : IsBoundedInProb
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => Real.sqrt (∫ omega,
      ‖(Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
            M.dominating omega).toReal)
          + Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
          scoreHat n X omega‖ ^ 2
      ∂M.dominating))
  /-- native Hellinger-weighted L2 score transport through the
  single vector square-root-density tangent expression. -/
  weightedScore_transport : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X =>
      Real.sqrt (∫ omega,
        ‖(Real.sqrt (((M.curve (estimator n X - theta0)).rnDeriv
              M.dominating omega).toReal)
              + Real.sqrt (((M.curve 0).rnDeriv M.dominating omega).toReal)) •
              scoreHat n X omega
          - (2 * Real.sqrt (((M.curve 0).rnDeriv
              M.dominating omega).toReal)) • score0 omega‖ ^ 2
        ∂M.dominating))
  /-- consistency in the native Euclidean parameter. -/
  consistency : TendstoInProbZero
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n X => estimator n X - theta0)

set_option maxHeartbeats 4000000 in
-- The RN/Bochner normalization proof elaborates several dependent Euclidean integrals.
/-- Native model-shift expansion normalized by the nonzero local-parameter norm.
The value at zero is explicitly defined to be zero.

Proof idea: the native consistency field localizes `M.qmd_limit`; the three
weighted-score fields respectively guarantee a genuine L2 object, supply the
`O_P(1)` factor, and identify the matrix cross moment through one CLM. -/
theorem qmdModel_modelShift_normalized_oP
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : HellingerScoreTransportHypVec P M estimator theta0 scoreHat score0) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        let delta := estimator n X - theta0
        if delta = 0 then 0 else
          ‖delta‖⁻¹ •
            (((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
                ∫ omega, scoreHat n X omega ∂P)
              - Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (qmdCrossMoment P M score0) delta)) := by
  let s : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal)
  let g : Omega → EuclideanSpace ℝ (Fin d) := M.score
  let r : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun delta omega =>
    s delta omega - s 0 omega - (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega
  let W : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega => (s (estimator n X - theta0) omega + s 0 omega) • scoreHat n X omega
  let K : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d) :=
    fun n X omega => W n X omega - (2 : ℝ) • (s 0 omega • score0 omega)
  let G0 : Omega → ℝ := fun omega => ‖g omega‖ * s 0 omega
  have hs : ∀ delta, MemLp (s delta) 2 M.dominating := fun delta => by
    letI := M.curve_isProbability delta
    simpa [s] using
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
        (M.curve_absContinuous delta)
  have hPac : P ≪ M.dominating := by
    simpa only [← M.curve_at_zero] using M.curve_absContinuous 0
  have hgP : MemLp g 2 P := by simpa [g] using M.score_memLp
  have hG0 : MemLp G0 2 M.dominating := by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
      hPac hgP.norm
    simpa [G0, s, g, M.curve_at_zero, smul_eq_mul, mul_comm] using hm
  have hscore0s0 : MemLp (fun omega => s 0 omega • score0 omega) 2 M.dominating := by
    simpa [s, M.curve_at_zero] using
      memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
        hPac h.score0_memLp
  have hr : ∀ delta, MemLp (r delta) 2 M.dominating := fun delta => by
    have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
      hPac (MemLp.const_inner (𝕜 := ℝ) delta hgP)
    have ht : MemLp (fun omega =>
        (1 / 2 : ℝ) * ⟪delta, g omega⟫_ℝ * s 0 omega) 2 M.dominating := by
      simpa [s, g, M.curve_at_zero, smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm] using hm.const_mul (1 / 2 : ℝ)
    exact (hs delta).sub (hs 0) |>.sub (by simpa [r] using ht)
  let qraw : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖
  let q : EuclideanSpace ℝ (Fin d) → ℝ := fun delta =>
    if delta = 0 then 0 else qraw delta
  have hqraw : Tendsto qraw (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
      M.qmd_limit
    simp only [Function.comp_def, ENNReal.toReal_zero] at ht
    refine ht.congr' (Eventually.of_forall fun delta => ?_)
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (norm_nonneg delta),
      ← AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal
        (hr delta)]
  have hq : Tendsto q (𝓝 (0 : EuclideanSpace ℝ (Fin d))) (𝓝 0) :=
    tendsto_zeroExtension qraw q hqraw (by simp [q]) (by intro x hx; simp [q, hx])
  have hq_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => q (estimator n X - theta0)) :=
    tendstoInProbZero_comp_zero h.consistency hq
  have hW_tight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating)) := by
    simpa only [W, s] using h.weightedScore_tight
  have hterm1 := tendstoInProbZero_of_isBoundedInProb_mul hW_tight hq_prob
  have hK_prob : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt (∫ omega, ‖K n X omega‖ ^ 2 ∂M.dominating)) := by
    simpa only [K, W, s, smul_smul] using h.weightedScore_transport
  have hterm2 := tendstoInProbZero_const_smul
    (Real.sqrt (∫ omega, G0 omega ^ 2 ∂M.dominating) / 2) hK_prob
  have henv := tendstoInProbZero_add hterm1 hterm2
  refine tendstoInProbZero_mono (fun n X => ?_) henv
  simp only [q, qraw, smul_eq_mul]
  by_cases hdelta : estimator n X - theta0 = 0
  · simp only [hdelta, ↓reduceIte, norm_zero, mul_zero, zero_add]
    exact norm_nonneg _
  · simp only [hdelta, ↓reduceIte]
    let delta := estimator n X - theta0
    have hdelta' : delta ≠ 0 := hdelta
    have hWmem : MemLp (W n X) 2 M.dominating := h.weightedScore_memLp n X
    have hKmem : MemLp (K n X) 2 M.dominating := by
      exact hWmem.sub (hscore0s0.const_smul (2 : ℝ))
    let fdelta : Omega → ℝ := fun omega => ⟪delta, g omega⟫_ℝ * s 0 omega
    have hfdelta : MemLp fdelta 2 M.dominating := by
      have hm := memLp_sqrt_rnDeriv_smul_of_memLp (P := P) (mu := M.dominating)
        hPac (MemLp.const_inner (𝕜 := ℝ) delta hgP)
      simpa [fdelta, s, g, M.curve_at_zero, smul_eq_mul, mul_comm] using hm
    have hshift :
        ((∫ omega, scoreHat n X omega ∂(M.curve delta)) -
            ∫ omega, scoreHat n X omega ∂P) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (qmdCrossMoment P M score0) delta =
        ∫ omega, r delta omega • W n X omega ∂M.dominating +
          (1 / 2 : ℝ) • ∫ omega, fdelta omega • K n X omega ∂M.dominating := by
      rw [qmdCrossMoment_apply M score0 h.score0_memLp delta]
      letI := M.curve_isProbability delta
      have hi_delta := (integrable_rnDeriv_smul_iff
        (M.curve_absContinuous delta)).2 (h.scoreHat_integrable_moving n X)
      have hi_zero := (integrable_rnDeriv_smul_iff hPac).2
        (h.scoreHat_integrable_truth n X)
      have hi_cross : Integrable (fun omega => ⟪delta, g omega⟫_ℝ • score0 omega) P :=
        memLp_one_iff_integrable.mp
          (h.score0_memLp.smul (MemLp.const_inner (𝕜 := ℝ) delta hgP) :
            MemLp _ 1 P)
      have hi_cross' : Integrable
          (fun omega => ⟪delta, M.score omega⟫_ℝ • score0 omega) P := by
        simpa only [g] using hi_cross
      have hi_cross_mu := (integrable_rnDeriv_smul_iff hPac).2 hi_cross'
      have hi1 : Integrable (fun omega => r delta omega • W n X omega)
          M.dominating :=
        memLp_one_iff_integrable.mp
          (hWmem.smul (hr delta) : MemLp _ 1 M.dominating)
      have hi2 : Integrable (fun omega => fdelta omega • K n X omega)
          M.dominating :=
        memLp_one_iff_integrable.mp
          (hKmem.smul hfdelta : MemLp _ 1 M.dominating)
      have hi2c : Integrable
          (fun omega => (1 / 2 : ℝ) • (fdelta omega • K n X omega)) M.dominating :=
        memLp_one_iff_integrable.mp
          ((hKmem.smul hfdelta : MemLp _ 1 M.dominating).const_smul (1 / 2 : ℝ))
      rw [← integral_rnDeriv_smul (M.curve_absContinuous delta),
        ← integral_rnDeriv_smul hPac, ← integral_rnDeriv_smul hPac,
        ← integral_sub hi_delta hi_zero]
      rw [← integral_sub]
      · rw [← integral_smul, ← integral_add hi1 hi2c]
        refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
        simp only [r, W, K, fdelta, s, g]
        rw [M.curve_at_zero]
        have hd := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ ((M.curve delta).rnDeriv M.dominating omega).toReal)
        have h0 := Real.sq_sqrt (ENNReal.toReal_nonneg :
          0 ≤ (P.rnDeriv M.dominating omega).toReal)
        simpa only [hd, h0, smul_smul, delta, mul_comm] using
          vector_sqrt_transport_identity
          (Real.sqrt (((M.curve delta).rnDeriv M.dominating omega).toReal))
          (Real.sqrt ((P.rnDeriv M.dominating omega).toReal))
          ⟪delta, M.score omega⟫_ℝ (scoreHat n X omega) (score0 omega)
      · simpa [Pi.sub_apply] using hi_delta.sub hi_zero
      · exact hi_cross_mu
    have hpoint : ∀ omega, fdelta omega ^ 2 ≤ ‖delta‖ ^ 2 * G0 omega ^ 2 := by
      intro omega
      have hinner := abs_real_inner_le_norm delta (g omega)
      have hsquare : ⟪delta, g omega⟫_ℝ ^ 2 ≤ (‖delta‖ * ‖g omega‖) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg ⟪delta, g omega⟫_ℝ)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
      simp only [fdelta, G0]
      calc
        (⟪delta, g omega⟫_ℝ * s 0 omega) ^ 2 =
            ⟪delta, g omega⟫_ℝ ^ 2 * s 0 omega ^ 2 := by ring
        _ ≤ (‖delta‖ * ‖g omega‖) ^ 2 * s 0 omega ^ 2 :=
          mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
        _ = ‖delta‖ ^ 2 * (‖g omega‖ * s 0 omega) ^ 2 := by ring
    rw [hshift, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg delta))]
    have henv_nonneg : 0 ≤
        Real.sqrt (∫ omega, ‖W n X omega‖ ^ 2 ∂M.dominating) *
            (Real.sqrt (∫ omega, r delta omega ^ 2 ∂M.dominating) / ‖delta‖) +
          Real.sqrt (∫ omega, G0 omega ^ 2 ∂M.dominating) / 2 *
            Real.sqrt (∫ omega, ‖K n X omega‖ ^ 2 ∂M.dominating) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg henv_nonneg]
    exact native_modelShift_normalized_bound (μ := M.dominating) (delta := delta)
      hdelta' (hr delta) hfdelta hG0 hWmem hKmem hpoint

/-- Ordinary native model-shift expansion from root-`n` tightness.

The cross moment acts through one matrix/continuous-linear-map expression; no
coordinatewise inverse or scalar discharge appears in the statement.

Proof idea: apply `qmdModel_modelShift_normalized_oP` and multiply its native
remainder by the `O_P(1)` root-`n` local parameter supplied by `hTight`. -/
theorem qmdModel_modelShift_oP_of_sqrtN_tight
    {d : ℕ} {P : Measure Omega} [IsProbabilityMeasure P]
    {M : QMDModel (Omega := Omega) P d}
    {estimator : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    {scoreHat : ∀ n, (Fin n → Omega) → Omega → EuclideanSpace ℝ (Fin d)}
    {score0 : Omega → EuclideanSpace ℝ (Fin d)}
    (h : HellingerScoreTransportHypVec P M estimator theta0 scoreHat score0)
    -- root-`n` tightness of the native local parameter.
    (hTight : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n • (estimator n X - theta0))) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        Real.sqrt n •
            ((∫ omega, scoreHat n X omega ∂P) -
              ∫ omega, scoreHat n X omega
                ∂(M.curve (estimator n X - theta0)))
          + Real.sqrt n •
              (Matrix.toEuclideanCLM (𝕜 := ℝ)
                (qmdCrossMoment P M score0) (estimator n X - theta0))) := by
  have hnorm := qmdModel_modelShift_normalized_oP h
  have hscale : IsBoundedInProb (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => Real.sqrt n * ‖estimator n X - theta0‖) := by
    simpa only [IsBoundedInProb, norm_smul, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)] using hTight
  have hprod := tendstoInProbZero_of_isBoundedInProb_mul hscale hnorm
  have hneg := tendstoInProbZero_const_smul (-1) hprod
  convert hneg using 1
  funext n X
  let delta := estimator n X - theta0
  by_cases hdelta : delta = 0
  · simp [delta, hdelta, M.curve_at_zero]
  · simp only [delta, hdelta, ↓reduceIte]
    have hnorm : ‖estimator n X - theta0‖ ≠ 0 := by
      simpa only [delta] using norm_ne_zero_iff.mpr hdelta
    have hcancel :
        Real.sqrt n * ‖estimator n X - theta0‖ *
            ‖estimator n X - theta0‖⁻¹ = Real.sqrt n := by
      field_simp [hnorm]
    simp only [smul_smul, hcancel]
    module

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
