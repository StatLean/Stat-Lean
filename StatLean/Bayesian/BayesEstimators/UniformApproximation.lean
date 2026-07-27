import StatLean.Bayesian.BayesEstimators.Defs
import StatLean.Bayesian.BayesEstimators.PosteriorTails
import StatLean.Bayesian.BernsteinVonMises.Theorem10_1

/-!
# Uniform approximation of the recentred posterior-risk process

Part 3 of the proof of vdV Theorem 10.8, in recentred form: after the change of variables
`t = τ + Δₙ`, the posterior-risk process approximates the **deterministic** limit criterion
`g = bpeGaussCriterion` uniformly over balls, in `P^n_{θ₀}`-probability:

* `lintegral_loss_bvmGaussian` — the exact recentring identity
  `∫ ℓ(t − h) dN(Δₙ, J⁻¹)(h) = g(t − Δₙ)` (translation pushforward);
* `posteriorRisk_shifted_majorant` — the majorant form of the uniform approximation:
  measurable `Mₙ(ω) → 0` in probability dominating the two-sided deviation
  `|Zₙ(τ + Δₙ) − g(τ)|` over `‖τ‖ ≤ R`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.3, proof of
Theorem 10.8, pp. 148–149 (the processes `Z_{n,M}`, `W_{n,M}` and their comparison).

**Proof formalization notes.** The deviation splits into (i) the truncated part
`∫_{‖h‖ ≤ Mₙ'} ℓ(τ + Δₙ − h) d(Post − N(Δₙ,J⁻¹))`, bounded by
`(sup_{ball} ℓ) · tvDist` (`lintegral_le_lintegral_add_tvDist` + Theorem 10.1); (ii) the
posterior tail, bounded by display (10.9) (`posterior_tail_lintegral_tendsto`); (iii) the
Gaussian tail, bounded by `gaussian_loss_convolution_lt_top`-style domination and score-sum
tightness. The book's `ℓ^∞(K)`-weak-convergence route (Corollary 5.58) is replaced by this
majorant statement — a formalization deviation recorded in `Theorem10_8.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)
open StatLean.Minimaxity (tvDist tvDist_comm tvDist_le_one)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Recentring identity**: the loss average against the random Gaussian is the
deterministic criterion evaluated at the recentred point,
`∫ ℓ(t − h) dN(Δₙ, J⁻¹)(h) = bpeGaussCriterion (t − Δₙ)`. -/
theorem lintegral_loss_bvmGaussian {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ) (n : ℕ) (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)) :
    ∫⁻ h, ℓ (t - h) ∂(bvmGaussian J sc n ω)
      = bpeGaussCriterion J ℓ (t - bvmEffScore J sc n ω) := by
  have hw : Measurable fun h : EuclideanSpace ℝ (Fin k) => ℓ (t - h) := hℓ.comp (by fun_prop)
  rw [bvmGaussian, bpeGaussCriterion,
    ← AsymptoticStatistics.multivariateGaussian_map_const_add J⁻¹ (bvmEffScore J sc n ω),
    lintegral_map hw (by fun_prop)]
  simp_rw [sub_add_eq_sub_sub]

/-! ### Elementary polynomial bookkeeping -/

/-- `1 + (a+b)ᵖ ≤ 2ᵖ (1+aᵖ)(1+bᵖ)` for nonnegative `a`, `b`, `p`: the multiplicative
splitting of the polynomial envelope used to detach the (random) centering from the
integration variable. -/
private lemma one_add_rpow_add_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    1 + (a + b) ^ p ≤ 2 ^ p * (1 + a ^ p) * (1 + b ^ p) := by
  have h2 : (1 : ℝ) ≤ 2 ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hp
  have h2p : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) p
  have hap : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
  have hbp : (0 : ℝ) ≤ b ^ p := Real.rpow_nonneg hb p
  have hmax : (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
    have hle : a + b ≤ 2 * max a b := by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have h0 : (0 : ℝ) ≤ max a b := le_trans ha (le_max_left a b)
    have hmm : (max a b) ^ p ≤ a ^ p + b ^ p := by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow (by linarith) hle hp
      _ = 2 ^ p * (max a b) ^ p := Real.mul_rpow (by norm_num) h0
      _ ≤ 2 ^ p * (a ^ p + b ^ p) := mul_le_mul_of_nonneg_left hmm h2p
  nlinarith [mul_nonneg (mul_nonneg h2p hap) hbp]

/-- The polynomially growing loss, evaluated at a point of norm at most `A + ‖h‖`, is
dominated by `2ᵖ(1+Aᵖ)` times the envelope `1 + ‖h‖ᵖ`. -/
private lemma poly_loss_le {p A : ℝ} (hp : 0 ≤ p) (hA : 0 ≤ A)
    {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hpoly : PolyGrowthLoss p ℓ)
    {x h : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ ≤ A + ‖h‖) :
    ℓ x ≤ ENNReal.ofReal (2 ^ p * (1 + A ^ p)) * ENNReal.ofReal (1 + ‖h‖ ^ p) := by
  have h2p : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) p
  have hAp : (0 : ℝ) ≤ A ^ p := Real.rpow_nonneg hA p
  have hpos : (0 : ℝ) ≤ 2 ^ p * (1 + A ^ p) := by positivity
  refine (hpoly x).trans ?_
  rw [← ENNReal.ofReal_mul hpos]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ‖x‖ ^ p ≤ (A + ‖h‖) ^ p := Real.rpow_le_rpow (norm_nonneg x) hx hp
  have h2 := one_add_rpow_add_le hA (norm_nonneg h) hp
  linarith

/-! ### The Gaussian approximation as a kernel (measurability of the deviation) -/

/-- The Gaussian family `m ↦ N(m, S)` as a kernel: the mean map is measurable because
`N(m,S) A = N(0,S) {x | m + x ∈ A}` is a section measure of a jointly measurable set. -/
private noncomputable def gaussMeanKernel (S : Matrix (Fin k) (Fin k) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) where
  toFun m := multivariateGaussian m S
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have hadd : Measurable fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        q.1 + q.2 := measurable_fst.add measurable_snd
    have hEq : ∀ m : EuclideanSpace ℝ (Fin k), multivariateGaussian m S t
        = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S
            (Prod.mk m ⁻¹' ((fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
              q.1 + q.2) ⁻¹' t)) := by
      intro m
      rw [← AsymptoticStatistics.multivariateGaussian_map_const_add S m,
        Measure.map_apply (by fun_prop) ht]
      rfl
    simp_rw [hEq]
    exact measurable_measure_prodMk_left (hadd ht)

private lemma gaussMeanKernel_apply (S : Matrix (Fin k) (Fin k) ℝ)
    (m : EuclideanSpace ℝ (Fin k)) : gaussMeanKernel S m = multivariateGaussian m S := rfl

private instance instIsMarkovKernel_gaussMeanKernel (S : Matrix (Fin k) (Fin k) ℝ) :
    IsMarkovKernel (gaussMeanKernel S) :=
  ⟨fun m => by rw [gaussMeanKernel_apply]; infer_instance⟩

/-- The random Gaussian approximation `ω ↦ N(Δₙ(ω), J⁻¹)` as a kernel. -/
private noncomputable def bvmGaussKernel (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ) :
    Kernel (Fin n → 𝓧) (EuclideanSpace ℝ (Fin k)) :=
  (gaussMeanKernel J⁻¹).comap (bvmEffScore J sc n) (measurable_bvmEffScore J hsc n)

private lemma bvmGaussKernel_apply (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ) (ω : Fin n → 𝓧) :
    bvmGaussKernel J hsc n ω = bvmGaussian J sc n ω := rfl

private lemma isMarkovKernel_bvmGaussKernel (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ) :
    IsMarkovKernel (bvmGaussKernel J hsc n) := by
  refine ⟨fun ω => ?_⟩
  rw [bvmGaussKernel_apply]
  change IsProbabilityMeasure (multivariateGaussian _ _)
  infer_instance

/-- Measurability of the Bernstein–von Mises deviation in the sample. -/
private lemma measurable_bvmTV (hsc : Measurable sc) (n : ℕ) :
    Measurable fun ω : Fin n → 𝓧 => bvmTV κ π θ₀ J sc n ω := by
  haveI := isMarkovKernel_bvmGaussKernel J hsc n (𝓧 := 𝓧)
  exact measurable_tvDist_kernel (bvmLocalPosterior κ π θ₀ n) (bvmGaussKernel J hsc n)

/-! ### Convergence in probability: sums, tight multiples, and rate extraction -/

/-- A sum of two quantities that vanish in probability vanishes in probability. -/
private lemma tendsto_prob_zero_add {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) {a b : ∀ n, Ω n → ℝ≥0∞}
    (ha : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => P n {ω | δ ≤ a n ω}) atTop (𝓝 0))
    (hb : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => P n {ω | δ ≤ b n ω}) atTop (𝓝 0))
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    Tendsto (fun n => P n {ω | δ ≤ a n ω + b n ω}) atTop (𝓝 0) := by
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hsub : ∀ n, {ω | δ ≤ a n ω + b n ω}
      ⊆ {ω | δ / 2 ≤ a n ω} ∪ {ω | δ / 2 ≤ b n ω} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    have hlt : a n ω + b n ω < δ / 2 + δ / 2 := ENNReal.add_lt_add hcon.1 hcon.2
    rw [ENNReal.add_halves] at hlt
    exact absurd hω (not_le.2 hlt)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n => P n {ω | δ / 2 ≤ a n ω} + P n {ω | δ / 2 ≤ b n ω})
    tendsto_const_nhds ?_ (fun n => zero_le _) (fun n => ?_)
  · simpa using (ha _ hhalf).add (hb _ hhalf)
  · exact (measure_mono (hsub n)).trans (measure_union_le _ _)

/-- A *tight* multiple of a quantity vanishing in probability still vanishes in
probability. -/
private lemma tendsto_prob_zero_mul_of_tight {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) {D T : ∀ n, Ω n → ℝ≥0∞}
    (hD : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ᶠ n in atTop, P n {ω | C < D n ω} ≤ ε)
    (hT : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => P n {ω | δ ≤ T n ω}) atTop (𝓝 0))
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    Tendsto (fun n => P n {ω | δ ≤ D n ω * T n ω}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨C, hC0, hCtop, hCev⟩ := hD (ε / 2) (ENNReal.div_pos hε.ne' (by norm_num))
  have hδC : 0 < δ / C := ENNReal.div_pos hδ.ne' hCtop
  have hTev : ∀ᶠ n in atTop, P n {ω | δ / C ≤ T n ω} ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.mp (hT _ hδC) (ε / 2) (ENNReal.div_pos hε.ne' (by norm_num))
  filter_upwards [hCev, hTev] with n h1 h2
  have hsub : {ω | δ ≤ D n ω * T n ω} ⊆ {ω | C < D n ω} ∪ {ω | δ / C ≤ T n ω} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_lt] at hcon
    have h3 : D n ω * T n ω ≤ C * T n ω := by gcongr; exact hcon.1
    have h4 : T n ω * C < δ / C * C := ENNReal.mul_lt_mul_left hC0 hCtop hcon.2
    rw [ENNReal.div_mul_cancel hC0 hCtop] at h4
    have h5 : C * T n ω < δ := by rwa [mul_comm] at h4
    exact absurd hω (not_le.2 (lt_of_le_of_lt h3 h5))
  calc P n {ω | δ ≤ D n ω * T n ω}
      ≤ P n ({ω | C < D n ω} ∪ {ω | δ / C ≤ T n ω}) := measure_mono hsub
    _ ≤ P n {ω | C < D n ω} + P n {ω | δ / C ≤ T n ω} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

/-- **Rate extraction.** From the *mean* convergence `∫ Tₙ dPₙ → 0` one produces a diverging
sequence `Mₙ → ∞` slow enough that `(1 + Mₙᵖ) Tₙ` still vanishes in probability (Markov's
inequality against the explicit rate `∫ Tₙ dPₙ`). -/
private lemma exists_slow_rate {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (T : ∀ n, Ω n → ℝ≥0∞) (hTmeas : ∀ n, Measurable (T n))
    (hfin : ∀ n, ∫⁻ ω, T n ω ∂(P n) ≠ ∞)
    (hint : Tendsto (fun n => ∫⁻ ω, T n ω ∂(P n)) atTop (𝓝 0))
    {p : ℝ} (hp : 0 ≤ p) :
    ∃ Mseq : ℕ → ℝ, Tendsto Mseq atTop atTop ∧ (∀ n, 0 ≤ Mseq n) ∧
      ∀ δ : ℝ≥0∞, 0 < δ →
        Tendsto (fun n => P n {ω | δ ≤ ENNReal.ofReal (1 + Mseq n ^ p) * T n ω})
          atTop (𝓝 0) := by
  sorry

/-! ### The Gaussian tails -/

/-- The polynomially weighted tails of the random Gaussian approximation vanish in
probability: after recentring, the measure is the deterministic `N(0,J⁻¹)`, whose weighted
tails vanish by dominated convergence, uniformly over the tight centering. -/
private lemma gaussTail_tendsto_prob
    (hPDF : IsPDFOf M μ) (hsc : Measurable sc)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    {p : ℝ} (hp : 0 ≤ p) {Mseq : ℕ → ℝ} (hMdiv : Tendsto Mseq atTop atTop)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    Tendsto (fun n => productMeasure M μ θ₀ n
        {ω | δ ≤ ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
          ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmGaussian J sc n ω)}) atTop (𝓝 0) := by
  sorry

/-- Tightness of the polynomial envelope factor `2ᵖ(1 + (R + ‖Δₙ‖)ᵖ)`. -/
private lemma tight_polyEnvelope
    (hPDF : IsPDFOf M μ) (hsc : Measurable sc)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    {p R : ℝ} (hp : 0 ≤ p) (hR : 0 ≤ R) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧ ∀ᶠ n in atTop, productMeasure M μ θ₀ n
      {ω | C < ENNReal.ofReal (2 ^ p * (1 + (R + ‖bvmEffScore J sc n ω‖) ^ p))} ≤ ε := by
  sorry

/-! ### The two-sided deviation bound at a fixed truncation radius -/

/-- **The per-`τ` estimate.** Splitting the local posterior at the ball of radius `ρ`, the
truncated parts are compared by total variation (the truncated loss is bounded by
`2ᵖ(1+(R+‖Δₙ‖)ᵖ)(1+ρᵖ)`) and the two tails are dominated by the polynomially weighted
tails of the posterior and of the Gaussian. -/
private lemma bpe_two_sided
    {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hℓ : Measurable ℓ) {p : ℝ} (hp : 0 ≤ p)
    (hpoly : PolyGrowthLoss p ℓ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ)
    (n : ℕ) (ω : Fin n → 𝓧) {τ : EuclideanSpace ℝ (Fin k)} (hτ : ‖τ‖ ≤ R) :
    bpePosteriorRisk κ π θ₀ ℓ n (τ + bvmEffScore J sc n ω) ω
        ≤ bpeGaussCriterion J ℓ τ
          + ENNReal.ofReal (2 ^ p * (1 + (R + ‖bvmEffScore J sc n ω‖) ^ p))
            * (ENNReal.ofReal (1 + ρ ^ p) * bvmTV κ π θ₀ J sc n ω
              + (∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ)ᶜ,
                    ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)
                + ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ)ᶜ,
                    ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmGaussian J sc n ω)))
      ∧ bpeGaussCriterion J ℓ τ
        ≤ bpePosteriorRisk κ π θ₀ ℓ n (τ + bvmEffScore J sc n ω) ω
          + ENNReal.ofReal (2 ^ p * (1 + (R + ‖bvmEffScore J sc n ω‖) ^ p))
            * (ENNReal.ofReal (1 + ρ ^ p) * bvmTV κ π θ₀ J sc n ω
              + (∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ)ᶜ,
                    ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)
                + ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ)ᶜ,
                    ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmGaussian J sc n ω))) := by
  classical
  haveI hGprob : IsProbabilityMeasure (bvmGaussian J sc n ω) := by
    change IsProbabilityMeasure (multivariateGaussian _ _)
    infer_instance
  set Δ := bvmEffScore J sc n ω with hΔ
  set Pn := bvmLocalPosterior κ π θ₀ n ω with hPn
  set Gn := bvmGaussian J sc n ω with hGn
  set s := Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ with hs
  set D := ENNReal.ofReal (2 ^ p * (1 + (R + ‖Δ‖) ^ p)) with hD
  set B := ENNReal.ofReal (1 + ρ ^ p) with hB
  set tv := bvmTV κ π θ₀ J sc n ω with htv
  set Tp := ∫⁻ h in sᶜ, ENNReal.ofReal (1 + ‖h‖ ^ p) ∂Pn with hTp
  set Tg := ∫⁻ h in sᶜ, ENNReal.ofReal (1 + ‖h‖ ^ p) ∂Gn with hTg
  have hsmeas : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hwmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) => ℓ (τ + Δ - h) :=
    hℓ.comp (by fun_prop)
  have hWmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (1 + ‖h‖ ^ p) := by
    have hrpow : Continuous fun t : ℝ => t ^ p :=
      continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr hp)
    exact (continuous_const.add (hrpow.comp continuous_norm)).measurable.ennreal_ofReal
  have hA0 : (0 : ℝ) ≤ R + ‖Δ‖ := by positivity
  -- the pointwise polynomial domination of the shifted loss
  have hpt : ∀ h, ℓ (τ + Δ - h) ≤ D * ENNReal.ofReal (1 + ‖h‖ ^ p) := by
    intro h
    rw [hD]
    refine poly_loss_le hp hA0 hpoly ?_
    calc ‖τ + Δ - h‖ ≤ ‖τ + Δ‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ ‖τ‖ + ‖Δ‖ + ‖h‖ := by gcongr; exact norm_add_le _ _
      _ ≤ R + ‖Δ‖ + ‖h‖ := by gcongr
  -- on the truncation ball the integrand is bounded
  have hballbd : ∀ h, s.indicator (fun h => ℓ (τ + Δ - h)) h ≤ D * B := by
    intro h
    by_cases hh : h ∈ s
    · rw [Set.indicator_of_mem hh]
      refine (hpt h).trans ?_
      have hnorm : ‖h‖ ≤ ρ := by
        rw [hs] at hh
        exact le_of_lt (mem_ball_zero_iff.mp hh)
      have hmono := Real.rpow_le_rpow (norm_nonneg h) hnorm hp
      rw [hB]
      gcongr
    · rw [Set.indicator_of_notMem hh]
      exact zero_le _
  -- the two truncated comparisons
  have hTVP : ∫⁻ h in s, ℓ (τ + Δ - h) ∂Pn
      ≤ ∫⁻ h in s, ℓ (τ + Δ - h) ∂Gn + D * B * tv := by
    rw [← lintegral_indicator hsmeas, ← lintegral_indicator hsmeas]
    exact lintegral_le_lintegral_add_tvDist Pn Gn (hwmeas.indicator hsmeas) hballbd
  have hTVG : ∫⁻ h in s, ℓ (τ + Δ - h) ∂Gn
      ≤ ∫⁻ h in s, ℓ (τ + Δ - h) ∂Pn + D * B * tv := by
    rw [← lintegral_indicator hsmeas, ← lintegral_indicator hsmeas]
    have h := lintegral_le_lintegral_add_tvDist Gn Pn (hwmeas.indicator hsmeas) hballbd
    have he : tvDist Gn Pn = tv := by rw [htv]; exact (tvDist_comm Pn Gn).symm
    rwa [he] at h
  -- the two tails
  have htailP : ∫⁻ h in sᶜ, ℓ (τ + Δ - h) ∂Pn ≤ D * Tp := by
    rw [hTp, ← lintegral_const_mul _ hWmeas]
    exact lintegral_mono hpt
  have htailG : ∫⁻ h in sᶜ, ℓ (τ + Δ - h) ∂Gn ≤ D * Tg := by
    rw [hTg, ← lintegral_const_mul _ hWmeas]
    exact lintegral_mono hpt
  -- the exact recentring identity
  have hgauss : ∫⁻ h, ℓ (τ + Δ - h) ∂Gn = bpeGaussCriterion J ℓ τ := by
    have h := lintegral_loss_bvmGaussian (J := J) (sc := sc) hℓ n ω (τ + Δ)
    rw [← hΔ, ← hGn, add_sub_cancel_right] at h
    exact h
  have hrisk : bpePosteriorRisk κ π θ₀ ℓ n (τ + Δ) ω = ∫⁻ h, ℓ (τ + Δ - h) ∂Pn := rfl
  have hexpand : D * (B * tv + (Tp + Tg)) = D * B * tv + D * Tp + D * Tg := by ring
  refine ⟨?_, ?_⟩
  · calc bpePosteriorRisk κ π θ₀ ℓ n (τ + Δ) ω
        = ∫⁻ h in s, ℓ (τ + Δ - h) ∂Pn + ∫⁻ h in sᶜ, ℓ (τ + Δ - h) ∂Pn := by
          rw [hrisk]; exact (lintegral_add_compl _ hsmeas).symm
      _ ≤ (∫⁻ h in s, ℓ (τ + Δ - h) ∂Gn + D * B * tv) + D * Tp := add_le_add hTVP htailP
      _ ≤ (∫⁻ h, ℓ (τ + Δ - h) ∂Gn + D * B * tv) + D * Tp := by
          gcongr
          exact Measure.restrict_le_self
      _ = bpeGaussCriterion J ℓ τ + (D * B * tv + D * Tp) := by rw [hgauss]; ring
      _ ≤ bpeGaussCriterion J ℓ τ + (D * B * tv + D * Tp + D * Tg) :=
          add_le_add le_rfl le_self_add
      _ = bpeGaussCriterion J ℓ τ + D * (B * tv + (Tp + Tg)) := by rw [hexpand]
  · calc bpeGaussCriterion J ℓ τ
        = ∫⁻ h in s, ℓ (τ + Δ - h) ∂Gn + ∫⁻ h in sᶜ, ℓ (τ + Δ - h) ∂Gn := by
          rw [← hgauss]; exact (lintegral_add_compl _ hsmeas).symm
      _ ≤ (∫⁻ h in s, ℓ (τ + Δ - h) ∂Pn + D * B * tv) + D * Tg := add_le_add hTVG htailG
      _ ≤ (∫⁻ h, ℓ (τ + Δ - h) ∂Pn + D * B * tv) + D * Tg := by
          gcongr
          exact Measure.restrict_le_self
      _ = bpePosteriorRisk κ π θ₀ ℓ n (τ + Δ) ω + (D * B * tv + D * Tg) := by
          rw [hrisk]; ring
      _ ≤ bpePosteriorRisk κ π θ₀ ℓ n (τ + Δ) ω + (D * B * tv + D * Tp + D * Tg) := by
          refine add_le_add le_rfl ?_
          rw [add_right_comm]
          exact le_self_add
      _ = bpePosteriorRisk κ π θ₀ ℓ n (τ + Δ) ω + D * (B * tv + (Tp + Tg)) := by rw [hexpand]

/-- **Majorant-form uniform approximation** (vdV pp. 148–149, recentred): there are
measurable `Mₙ : (Fin n → 𝓧) → ℝ≥0∞` vanishing in `P^n_{θ₀}`-probability such that on the
ball `‖τ‖ ≤ R`, the recentred posterior risk `Zₙ(τ + Δₙ)` and the deterministic criterion
`g(τ)` differ by at most `Mₙ` in both directions. -/
theorem posteriorRisk_shifted_majorant
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the tests condition (10.2); vdV Thm 10.1
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV Thm 10.1
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ) {p : ℝ}
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    {R : ℝ}
    -- LEAN-ONLY: nontrivial approximation radius
    (hR : 0 < R) :
    ∃ Mn : ∀ n : ℕ, (Fin n → 𝓧) → ℝ≥0∞,
      (∀ n, Measurable (Mn n)) ∧
      (∀ δ : ℝ≥0∞, 0 < δ →
        Tendsto (fun n => productMeasure M μ θ₀ n {ω | δ ≤ Mn n ω}) atTop (𝓝 0)) ∧
      ∀ n (ω : Fin n → 𝓧) (τ : EuclideanSpace ℝ (Fin k)), ‖τ‖ ≤ R →
        bpePosteriorRisk κ π θ₀ ℓ n (τ + bvmEffScore J sc n ω) ω
            ≤ bpeGaussCriterion J ℓ τ + Mn n ω ∧
          bpeGaussCriterion J ℓ τ
            ≤ bpePosteriorRisk κ π θ₀ ℓ n (τ + bvmEffScore J sc n ω) ω + Mn n ω := by
  classical
  haveI hPn : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ₀ n
  have hrpow : Continuous fun t : ℝ => t ^ p :=
    continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x p (Or.inr hp)
  have hWmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (1 + ‖h‖ ^ p) :=
    (continuous_const.add (hrpow.comp continuous_norm)).measurable.ennreal_ofReal
  -- the Bernstein–von Mises deviation is measurable, bounded by `1`, and vanishes in mean
  have htvmeas : ∀ n : ℕ, Measurable fun ω : Fin n → 𝓧 => bvmTV κ π θ₀ J sc n ω :=
    fun n => measurable_bvmTV hsc n
  have htvle : ∀ (n : ℕ) (ω : Fin n → 𝓧), bvmTV κ π θ₀ J sc n ω ≤ 1 := by
    intro n ω
    haveI : IsProbabilityMeasure (bvmGaussian J sc n ω) := by
      change IsProbabilityMeasure (multivariateGaussian _ _)
      infer_instance
    exact tvDist_le_one _ _
  have htvfin : ∀ n : ℕ,
      ∫⁻ ω, bvmTV κ π θ₀ J sc n ω ∂(productMeasure M μ θ₀ n) ≠ ∞ := by
    intro n
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ ω, bvmTV κ π θ₀ J sc n ω ∂(productMeasure M μ θ₀ n)
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(productMeasure M μ θ₀ n) := lintegral_mono (htvle n)
      _ = 1 := by simp
  -- Step 1: a diverging truncation radius, slow enough for the (rate-free) BvM convergence
  obtain ⟨Mseq, hMdiv, hMnn, hrate⟩ :=
    exists_slow_rate (fun n => productMeasure M μ θ₀ n)
      (fun n ω => bvmTV κ π θ₀ J sc n ω) htvmeas htvfin
      (bernstein_von_mises_lintegral hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ) hp
  -- Step 2: exponentially powerful tests for this radius sequence, hence display (10.9)
  obtain ⟨φ, c, hc, hφ⟩ := exponential_tests hPDF hsc hDQM hJ_pd hJ hTests hMdiv
  have hTp := posterior_tail_lintegral_tendsto hPDF hsc hDQM hJ_pd hJ hκ hM_joint hπ hp hmom
    hMdiv hc hφ
  -- Step 3: the Gaussian tails
  have hTg : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun n => productMeasure M μ θ₀ n
      {ω | δ ≤ ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
        ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmGaussian J sc n ω)}) atTop (𝓝 0) :=
    fun δ hδ => gaussTail_tendsto_prob hPDF hsc hDQM hJ_pd hJ hp hMdiv δ hδ
  refine ⟨fun n ω => ENNReal.ofReal (2 ^ p * (1 + (R + ‖bvmEffScore J sc n ω‖) ^ p))
      * (ENNReal.ofReal (1 + Mseq n ^ p) * bvmTV κ π θ₀ J sc n ω
        + (∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
              ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)
          + ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
              ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmGaussian J sc n ω))), ?_, ?_, ?_⟩
  · -- measurability
    intro n
    have h1 : Measurable fun ω : Fin n → 𝓧 =>
        ENNReal.ofReal (2 ^ p * (1 + (R + ‖bvmEffScore J sc n ω‖) ^ p)) := by
      have hcont : Continuous fun x : ℝ => 2 ^ p * (1 + (R + x) ^ p) :=
        continuous_const.mul (continuous_const.add
          (hrpow.comp (continuous_const.add continuous_id)))
      exact (hcont.measurable.comp (measurable_bvmEffScore J hsc n).norm).ennreal_ofReal
    have h3 : Measurable fun ω : Fin n → 𝓧 =>
        ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
          ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω) :=
      Measurable.setLIntegral_kernel hWmeas Metric.isOpen_ball.measurableSet.compl
    have h4 : Measurable fun ω : Fin n → 𝓧 =>
        ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
          ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmGaussian J sc n ω) := by
      haveI := isMarkovKernel_bvmGaussKernel J hsc n (𝓧 := 𝓧)
      exact Measurable.setLIntegral_kernel (κ := bvmGaussKernel J hsc n) hWmeas
        Metric.isOpen_ball.measurableSet.compl
    exact h1.mul (((htvmeas n).const_mul _).add (h3.add h4))
  · -- vanishing in probability
    intro δ hδ
    refine tendsto_prob_zero_mul_of_tight (fun n => productMeasure M μ θ₀ n)
      (fun ε hε => tight_polyEnvelope hPDF hsc hDQM hJ_pd hJ hp hR.le ε hε)
      (fun δ' hδ' => tendsto_prob_zero_add _ hrate
        (fun δ'' hδ'' => tendsto_prob_zero_add _ hTp hTg δ'' hδ'') δ' hδ') δ hδ
  · -- the two-sided deviation bound
    exact fun n ω τ hτ => bpe_two_sided hℓ hp hpoly hR.le (hMnn n) n ω hτ

end StatLean.Bayesian
