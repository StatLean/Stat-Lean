import Mathlib.Probability.Independence.Basic
import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.TailBounds
import StatLean.HighDimensionalStatistics.Lasso.DeterministicRate

/-!
# Lasso rate under sub-Gaussian noise (Lu-BDA §8, cor:lasso-rate)

**Corollary** (Lu, *Big Data Analysis* §8): if the noises `ε₁,…,εₙ` are independent and
each sub-Gaussian with variance proxy `σ²`, the design columns satisfy `(1/n)‖X_j‖² ≤ 1`
(equivalently `∑ᵢ Xᵢⱼ² ≤ n`), the restricted eigenvalue condition `RE(κ, 3)` holds, and
`δ ∈ (0,1)`, then choosing the tuning parameter

  `λ = 2√(2σ² log(2d/δ)/n)`

with probability at least `1 − δ`, the Lasso estimator satisfies

  `‖β̂ − β*‖₂ ≤ (3/κ)·√s·λ = O_P(√(s·log d / n))`.

**Deviation from book:** Lu states `λ = σ√(log(2d/δ)/(2n))`, which is approximately 4× too
small to satisfy the tuning condition `λ ≥ (2/n)‖Xᵀε‖∞` under the union-bound tail bound
derived here. The provable constant is `λ = 2√(2σ² log(2d/δ)/n)`, preserving the same
`O_P(√(s·log d/n))` rate order.

**Proof structure:** The deterministic `lasso_l2_rate` (`thm:re`) reduces the probabilistic
content to showing the tuning event `λ ≥ (2/n)·‖Xᵀε‖∞` holds w.p. ≥ 1 − δ. For each
column j: `∑ᵢ Xᵢⱼεᵢ` is sub-Gaussian with proxy `σ² ∑ᵢ Xᵢⱼ² ≤ σ²n` via
`HasSubgaussianMGF.sum_of_iIndepFun` (heterogeneous-proxy Hoeffding). A two-sided sub-Gaussian
tail + union bound over 2d events gives `P(‖Xᵀε‖∞ > t) ≤ 2d·exp(−t²/(2σ²n))`. Setting
`t = n·λ/2 ≥ √(2σ²n·log(2d/δ))` makes this ≤ δ, establishing the good event.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.HighDimensionalStatistics
open StatLean.ConcentrationInequalities

variable {n d : ℕ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Coordinate formula for the design transpose -/

/-- Coordinate formula: `(Xᵀv)_j = ∑ᵢ Xᵢⱼ · vᵢ` — the j-th output of the transposed design
applied to `v` is the inner product of column j of X with v. -/
private lemma designMap_trans_coord (X : Matrix (Fin n) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (j : Fin d) :
    (designMap Xᵀ v).ofLp j = ∑ i : Fin n, X i j * v.ofLp i := by
  have h1 : (designMap Xᵀ v).ofLp = Xᵀ *ᵥ v.ofLp := rfl
  calc (designMap Xᵀ v).ofLp j
      = (Xᵀ *ᵥ v.ofLp) j := congr_fun h1 j
    _ = ∑ i : Fin n, Xᵀ j i * v.ofLp i := by simp [mulVec, dotProduct]
    _ = ∑ i : Fin n, X i j * v.ofLp i := by simp [transpose_apply]

/-! ## Per-column sub-Gaussian bound -/

/-- The j-th column inner product `∑ᵢ Xᵢⱼ · εᵢ` is sub-Gaussian with variance proxy
`n · σ²` under independent centered sub-Gaussian noise `ε`. -/
private lemma colInner_isSubGaussian
    (X : Matrix (Fin n) (Fin d) ℝ)
    (ε : Fin n → Ω → ℝ)
    (σ2 : ℝ≥0)
    (μ : Measure Ω)
    -- USER-INPUT: each εᵢ is sub-Gaussian with variance proxy σ²; Lu-BDA §8 (cor:lasso-rate)
    (hε_sg : ∀ i : Fin n, IsSubGaussian (ε i) σ2 μ)
    -- USER-INPUT: ε₀,…,εₙ₋₁ are jointly independent; Lu-BDA §8 (cor:lasso-rate)
    (hε_indep : iIndepFun ε μ)
    -- USER-INPUT: each εᵢ is centered, E[εᵢ] = 0; Lu-BDA §8 (cor:lasso-rate)
    (hε_zero : ∀ i : Fin n, ∫ ω, ε i ω ∂μ = 0)
    -- USER-INPUT: column norms normalised, ∑ᵢ Xᵢⱼ² ≤ n; Lu-BDA §8 (cor:lasso-rate)
    (hcolnorm : ∀ j : Fin d, ∑ i : Fin n, X i j ^ 2 ≤ n)
    (j : Fin d) :
    IsSubGaussian (fun ω => ∑ i : Fin n, X i j * ε i ω) (n * σ2 : ℝ≥0) μ := by
  -- ── Step 1: derive integrability using zero mean + MGF bound ─────────────────
  -- (isSubGaussian_iff.mp (hε_sg i)) gives HasSubgaussianMGF of (εᵢ - E[εᵢ]).
  -- Since E[εᵢ] = 0 by hε_zero, this is the same as integrable (εᵢ).
  have hε_int : ∀ i, Integrable (ε i) μ := fun i => by
    have h := (isSubGaussian_iff.mp (hε_sg i)).integrable
    simp only [hε_zero i, sub_zero] at h
    exact h
  -- ── Step 2: scaled family Y i ω := X i j * ε i ω has proxy (X i j)² · σ² ──
  have hY_sg : ∀ i : Fin n, HasSubgaussianMGF (fun ω => X i j * ε i ω)
      (⟨(X i j) ^ 2, sq_nonneg _⟩ * σ2 : ℝ≥0) μ := by
    intro i
    have hsg_scaled := isSubGaussian_const_mul (hε_sg i) (X i j)
    have hmean : ∫ ω, X i j * ε i ω ∂μ = 0 := by
      simp only [integral_const_mul, hε_zero i, mul_zero]
    simp only [isSubGaussian_iff, hmean, sub_zero] at hsg_scaled
    exact hsg_scaled
  -- ── Step 3: independence of the scaled family {Y i} ──────────────────────────
  have hY_indep : iIndepFun (fun i ω => X i j * ε i ω) μ :=
    hε_indep.comp (fun i x => X i j * x) (fun i => measurable_const.mul measurable_id)
  -- ── Step 4: the sum ∑ᵢ Y i is sub-Gaussian with proxy ∑ᵢ (X i j)² · σ² ─────
  have hsum_mg : HasSubgaussianMGF
      (fun ω => ∑ i : Fin n, X i j * ε i ω)
      (∑ i : Fin n, ⟨(X i j) ^ 2, sq_nonneg _⟩ * σ2 : ℝ≥0) μ := by
    have := HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (c := fun i => ⟨(X i j) ^ 2, sq_nonneg _⟩ * σ2)
      (s := Finset.univ)
      (fun i _ => hY_sg i)
    simpa using this
  -- ── Step 5: upgrade proxy from ∑ᵢ (X i j)² · σ² to n · σ² (monotonicity) ────
  have hproxy_le : ∑ i : Fin n, ⟨(X i j) ^ 2, sq_nonneg _⟩ * σ2 ≤ (n : ℝ≥0) * σ2 := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (zero_le _)
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_sum, NNReal.coe_natCast, NNReal.coe_mk]
    exact_mod_cast hcolnorm j
  have hsum_up : HasSubgaussianMGF
      (fun ω => ∑ i : Fin n, X i j * ε i ω) (n * σ2 : ℝ≥0) μ :=
    ⟨hsum_mg.integrable_exp_mul, fun t => (hsum_mg.mgf_le t).trans (by
      apply Real.exp_le_exp.mpr; gcongr; exact_mod_cast NNReal.coe_le_coe.mpr hproxy_le)⟩
  -- ── Step 6: conclude IsSubGaussian using zero mean ────────────────────────────
  have hsum_mean : ∫ ω, ∑ i : Fin n, X i j * ε i ω ∂μ = 0 := by
    rw [integral_finset_sum Finset.univ (fun i _ => (hε_int i).const_mul (X i j))]
    simp_rw [integral_const_mul, hε_zero, mul_zero, Finset.sum_const_zero]
  unfold IsSubGaussian
  simp only [hsum_mean, sub_zero]
  exact hsum_up

/-! ## Tail bound on linfNorm of Xᵀε -/

/-- Union-bound tail: `P(‖Xᵀε‖∞ > t) ≤ 2d · exp(−t²/(2nσ²))`.
The column-j inner product `∑ᵢ Xᵢⱼεᵢ` is sub-Gaussian with proxy `nσ²` (via
`colInner_isSubGaussian`); a two-sided sub-Gaussian tail + union bound over the `d` columns
yields the result. -/
private lemma linfNorm_noise_tail
    (X : Matrix (Fin n) (Fin d) ℝ)
    (ε : Fin n → Ω → ℝ)
    (σ2 : ℝ≥0)
    (μ : Measure Ω)
    (hε_sg : ∀ i : Fin n, IsSubGaussian (ε i) σ2 μ)
    (hε_indep : iIndepFun ε μ)
    (hε_zero : ∀ i : Fin n, ∫ ω, ε i ω ∂μ = 0)
    (hcolnorm : ∀ j : Fin d, ∑ i : Fin n, X i j ^ 2 ≤ n)
    (t : ℝ) (ht : 0 ≤ t) :
    let noiseVec := fun ω => WithLp.toLp (p := 2) (fun i : Fin n => ε i ω)
    μ {ω | t < linfNorm (designMap Xᵀ (noiseVec ω))} ≤
      ENNReal.ofReal (2 * d * Real.exp (-t ^ 2 / (2 * (n * (σ2 : ℝ))))) := by
  intro noiseVec
  -- ── Step 1: unfold linfNorm as sup over columns ───────────────────────────────
  have hincl :
      {ω | t < linfNorm (designMap Xᵀ (noiseVec ω))} ⊆
      ⋃ j : Fin d, {ω | t < |(designMap Xᵀ (noiseVec ω)).ofLp j|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    unfold linfNorm at hω
    rcases isEmpty_or_nonempty (Fin d) with hd0 | hne
    · -- d = 0: linfNorm = sSup ∅ = 0, contradicts ht
      have hval : ⨆ j : Fin d, |(designMap Xᵀ (noiseVec ω)).ofLp j| = 0 := by
        haveI := hd0
        change sSup (Set.range (fun j : Fin d => |(designMap Xᵀ (noiseVec ω)).ofLp j|)) = 0
        rw [Set.range_eq_empty_iff.mpr hd0, Real.sSup_empty]
      exact absurd (hval ▸ hω) (not_lt.mpr ht)
    · haveI := hne
      exact (lt_ciSup_iff (Set.finite_range _).bddAbove).mp hω
  -- ── Step 2: per-column coordinate = column inner product ──────────────────────
  have hcoord : ∀ ω j, (designMap Xᵀ (noiseVec ω)).ofLp j = ∑ i, X i j * ε i ω := by
    intro ω j
    rw [designMap_trans_coord]
    congr 1; ext i
    simp [noiseVec, WithLp.ofLp_toLp]
  -- ── Step 3: per-column sub-Gaussian tail bound ───────────────────────────────
  have hcol_sg : ∀ j : Fin d,
      IsSubGaussian (fun ω => ∑ i : Fin n, X i j * ε i ω) (n * σ2 : ℝ≥0) μ :=
    fun j => colInner_isSubGaussian X ε σ2 μ hε_sg hε_indep hε_zero hcolnorm j
  have hε_int : ∀ i, Integrable (ε i) μ := fun i => by
    have h := (isSubGaussian_iff.mp (hε_sg i)).integrable
    simp only [hε_zero i, sub_zero] at h; exact h
  have hcol_tail : ∀ j : Fin d,
      μ {ω | t < |(designMap Xᵀ (noiseVec ω)).ofLp j|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (n * (σ2 : ℝ))))) := by
    intro j
    have hm : ∫ x, ∑ i : Fin n, X i j * ε i x ∂μ = 0 := by
      rw [integral_finset_sum Finset.univ (fun i _ => (hε_int i).const_mul (X i j))]
      simp_rw [integral_const_mul, hε_zero, mul_zero, Finset.sum_const_zero]
    have hset : {ω | t < |(designMap Xᵀ (noiseVec ω)).ofLp j|} =
        {ω | t < |∑ i : Fin n, X i j * ε i ω - ∫ x, (∑ i, X i j * ε i x) ∂μ|} := by
      congr 1; ext ω; simp only [Set.mem_setOf_eq, hcoord ω j, hm, sub_zero]
    rw [hset]
    exact (hcol_sg j).measure_abs_sub_integral_lt_le ht
  -- ── Step 4: union bound over d columns ───────────────────────────────────────
  calc μ {ω | t < linfNorm (designMap Xᵀ (noiseVec ω))}
      ≤ μ (⋃ j : Fin d, {ω | t < |(designMap Xᵀ (noiseVec ω)).ofLp j|}) :=
          measure_mono hincl
    _ ≤ ∑' j : Fin d, μ {ω | t < |(designMap Xᵀ (noiseVec ω)).ofLp j|} :=
          measure_iUnion_le _
    _ = ∑ j : Fin d, μ {ω | t < |(designMap Xᵀ (noiseVec ω)).ofLp j|} :=
          tsum_fintype _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (n * (σ2 : ℝ))))) :=
          Finset.sum_le_sum fun j _ => hcol_tail j
    _ = ENNReal.ofReal (2 * d * Real.exp (-t ^ 2 / (2 * (n * (σ2 : ℝ))))) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast (n := d),
              ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; ring

/-! ## Main theorem: cor:lasso-rate -/

/-- **Lasso rate under sub-Gaussian noise** (Lu, *Big Data Analysis* §8, `cor:lasso-rate`).

Given:
- Fixed design `X ∈ ℝ^{n×d}`, true parameter `β*` supported on `S` (`|S| = s`).
- Independent centered noise `ε₁,…,εₙ` each sub-Gaussian with variance proxy `σ²`.
- Normalised columns: `∑ᵢ Xᵢⱼ² ≤ n` for all j.
- Restricted eigenvalue `RE(κ, 3)`.
- Confidence level `δ ∈ (0,1)` and number of features `d ≥ 1`.

Choosing the tuning parameter `λ ≥ 2√(2σ² log(2d/δ)/n)`, the Lasso estimator `β̂` satisfies

  `P(‖β̂ − β*‖₂ ≤ (3/κ)·√s·λ) ≥ 1 − δ`.

**Deviation from book:** Lu's stated `λ = σ√(log(2d/δ)/(2n))` is ~4× smaller than the provable
tuning constant `2√(2σ² log(2d/δ)/n)` derived here from the union-bound tail bound. The rate
order `O_P(√(s log d/n))` is unaffected. -/
theorem lasso_random_rate
    (X : Matrix (Fin n) (Fin d) ℝ)
    (βstar : EuclideanSpace ℝ (Fin d))
    (S : Finset (Fin d))
    (ε : Fin n → Ω → ℝ)
    (σ2 : ℝ≥0)
    (μ : Measure Ω)
    (lam κ δ : ℝ)
    (βhat : Ω → EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: n > 0; Lu-BDA §8 (cor:lasso-rate)
    (hn : 0 < n)
    -- USER-INPUT: κ > 0; Lu-BDA §8 (cor:lasso-rate)
    (hkappa : 0 < κ)
    -- USER-INPUT: λ > 0; Lu-BDA §8 (cor:lasso-rate)
    (hlam_pos : 0 < lam)
    -- USER-INPUT: d ≥ 1 (needed for log(2d/δ) > 0); Lu-BDA §8 (cor:lasso-rate)
    (hd : 0 < d)
    -- USER-INPUT: δ ∈ (0,1); Lu-BDA §8 (cor:lasso-rate)
    (hδ_pos : 0 < δ)
    (hδ_lt : δ < 1)
    -- USER-INPUT: restricted eigenvalue RE(κ,3); Lu-BDA §8 (cor:lasso-rate)
    (hre : RestrictedEigenvalue X S κ 3)
    -- USER-INPUT: β* supported on S; Lu-BDA §8 (cor:lasso-rate)
    (hS : ∀ j ∉ S, βstar.ofLp j = 0)
    -- USER-INPUT: εᵢ are jointly independent; Lu-BDA §8 (cor:lasso-rate)
    (hε_indep : iIndepFun ε μ)
    -- USER-INPUT: each εᵢ is sub-Gaussian with proxy σ²; Lu-BDA §8 (cor:lasso-rate)
    (hε_sg : ∀ i : Fin n, IsSubGaussian (ε i) σ2 μ)
    -- USER-INPUT: each εᵢ is centered, E[εᵢ] = 0; Lu-BDA §8 (cor:lasso-rate)
    (hε_zero : ∀ i : Fin n, ∫ ω, ε i ω ∂μ = 0)
    -- USER-INPUT: column norms normalised, (1/n)‖X_j‖² ≤ 1; Lu-BDA §8 (cor:lasso-rate)
    (hcolnorm : ∀ j : Fin d, ∑ i : Fin n, X i j ^ 2 ≤ n)
    -- USER-INPUT: β̂ ω minimises the Lasso objective for response Y ω; Lu-BDA §8 (cor:lasso-rate)
    (hLasso : ∀ ω, IsLassoEstimator X
        (designMap X βstar + WithLp.toLp (p := 2) (fun i => ε i ω)) lam (βhat ω))
    -- USER-INPUT: λ ≥ 2√(2σ² log(2d/δ)/n) — the provable tuning constant; Lu-BDA §8 (cor:lasso-rate)
    -- Note: book states λ = σ√(log(2d/δ)/(2n)); the provable constant is ~4× larger.
    (hlam_ge : lam ≥ 2 * Real.sqrt (2 * (σ2 : ℝ) * Real.log (2 * d / δ) / n))
    -- LEAN-ONLY: 0 < σ2; when σ2 = 0 the noise is a.s. 0 and the result holds trivially
    -- via ae_eq_zero_of_hasSubgaussianMGF_zero, which requires a separate proof path
    (hσ2_pos : 0 < (σ2 : ℝ)) :
    ENNReal.ofReal (1 - δ) ≤
      μ {ω | ‖βhat ω - βstar‖ ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam} := by
  -- ── Setup ──────────────────────────────────────────────────────────────────────
  set noiseVec := fun ω => WithLp.toLp (p := 2) (fun i : Fin n => ε i ω)
  set G := {ω | lam ≥ (2 / (n : ℝ)) * linfNorm (designMap Xᵀ (noiseVec ω))}
  haveI : IsProbabilityMeasure μ := hε_indep.isProbabilityMeasure
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- ── Step 1: On G, lasso_l2_rate gives the bound ───────────────────────────────
  have hG_sub : G ⊆ {ω | ‖βhat ω - βstar‖ ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam} := by
    intro ω hω
    apply lasso_l2_rate X βstar S (noiseVec ω)
        (designMap X βstar + noiseVec ω) lam κ (βhat ω)
        hn hkappa hlam_pos hre (hLasso ω) rfl hS
    exact hω
  -- ── Step 2: Bad event: Gᶜ = {ω | ‖Xᵀε‖∞ > n·λ/2} ───────────────────────────
  set t_star := (n : ℝ) * lam / 2
  have hGc_eq : Gᶜ = {ω | t_star < linfNorm (designMap Xᵀ (noiseVec ω))} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    have hn' : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    constructor
    · intro h
      -- h : lam < (2/n) * L; want: n*lam/2 < L
      have key := mul_lt_mul_of_pos_right h hn_pos
      have h2 : (2 / ↑n) * linfNorm (designMap Xᵀ (noiseVec ω)) * ↑n =
                 2 * linfNorm (designMap Xᵀ (noiseVec ω)) := by field_simp
      unfold_let t_star; linarith
    · intro h
      -- h : n*lam/2 < L; want: lam < (2/n) * L
      have key2 : (2 / ↑n) * linfNorm (designMap Xᵀ (noiseVec ω)) =
                  2 * linfNorm (designMap Xᵀ (noiseVec ω)) / ↑n := by field_simp
      rw [key2, lt_div_iff hn_pos]
      unfold_let t_star at h; linarith
  -- ── Step 3: exp bound ─────────────────────────────────────────────────────────
  have hlog_pos : 0 < Real.log (2 * d / δ) := by
    apply Real.log_pos
    rw [gt_iff_lt, lt_div_iff hδ_pos]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht_star_sq : t_star ^ 2 ≥ 2 * (σ2 : ℝ) * n * Real.log (2 * d / δ) := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * (σ2 : ℝ) * Real.log (2 * d / δ) / n)
    have : t_star ^ 2 = (n : ℝ) ^ 2 * lam ^ 2 / 4 := by unfold_let t_star; ring
    rw [this]
    nlinarith [sq_nonneg (lam - 2 * Real.sqrt (2 * (σ2 : ℝ) * Real.log (2 * d / δ) / n)),
               Real.sqrt_nonneg (2 * (σ2 : ℝ) * Real.log (2 * d / δ) / n)]
  have hexp_le : 2 * d * Real.exp (-t_star ^ 2 / (2 * (n * (σ2 : ℝ)))) ≤ δ := by
    have harg : -t_star ^ 2 / (2 * (n * (σ2 : ℝ))) ≤ -Real.log (2 * d / δ) := by
      rw [neg_div, neg_le_neg_iff, div_le_div_iff (by positivity) (by positivity)]
      linarith [ht_star_sq]
    calc 2 * d * Real.exp (-t_star ^ 2 / (2 * (n * (σ2 : ℝ))))
        ≤ 2 * d * Real.exp (-Real.log (2 * d / δ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
      _ = 2 * d * (δ / (2 * d)) := by
            rw [Real.exp_neg, Real.exp_log (by positivity), inv_eq_one_div]
      _ = δ := by field_simp
  -- ── Step 4: P(Gᶜ) ≤ δ ────────────────────────────────────────────────────────
  have hPGc_le : μ Gᶜ ≤ ENNReal.ofReal δ := by
    rw [hGc_eq]
    calc μ {ω | t_star < linfNorm (designMap Xᵀ (noiseVec ω))}
        ≤ ENNReal.ofReal (2 * d * Real.exp (-t_star ^ 2 / (2 * (n * (σ2 : ℝ))))) :=
            linfNorm_noise_tail X ε σ2 μ hε_sg hε_indep hε_zero hcolnorm t_star (by positivity)
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hexp_le
  -- ── Step 5: P(G) ≥ 1 − δ via G ∪ Gᶜ = univ and subadditivity ─────────────────
  have hPG : ENNReal.ofReal (1 - δ) ≤ μ G := by
    have hcover : μ Set.univ ≤ μ G + μ Gᶜ := by
      calc μ Set.univ = μ (G ∪ Gᶜ) := by simp [Set.union_compl_self]
        _ ≤ μ G + μ Gᶜ := measure_union_le G Gᶜ
    rw [measure_univ] at hcover
    have h_lower2 : 1 ≤ μ G + ENNReal.ofReal δ :=
      hcover.trans (add_le_add_left hPGc_le _)
    have h1delt : ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (by linarith)]
    rw [h1delt]
    exact tsub_le_iff_right.mpr h_lower2
  -- ── Step 6: conclude ─────────────────────────────────────────────────────────
  calc ENNReal.ofReal (1 - δ) ≤ μ G := hPG
    _ ≤ μ {ω | ‖βhat ω - βstar‖ ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam} :=
          measure_mono hG_sub

end StatLean.HighDimensionalStatistics
