import StatLean.HighDimensionalStatistics.MEstimator.ScoreSubGaussian
import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.ConcentrationInequalities.SubGaussian.TailBounds

/-!
# High-probability good event for the GLM score (Wainwright Cor 9.26 proof, p. 288)

The probabilistic step that discharges the deterministic "good event" `𝔾(λ) = {Φ*(∇Lₙ(θ*)) ≤ λ/2}`
for the `ℓ₁`-regularized GLM. Since `Φ* = ℓ∞` and `∇Lₙ(θ*) = scoreVec`, the good event is
`{‖scoreVec‖∞ ≤ λ/2}`. A two-sided sub-Gaussian tail on each coordinate (`score_coord_isSubGaussian`,
proxy `B²C²/n`) + a union bound over the `d` coordinates gives
`P(‖scoreVec‖∞ > t) ≤ 2d·exp(−t²/(2B²C²/n))`; choosing `λ = 4BC{√(log d/n) + δ}` and `t = λ/2` makes
this `≤ 2exp(−2nδ²)`. Structurally identical to `Lasso/RandomNoise.lean` (`linfNorm_noise_tail` +
the good-event split of `lasso_random_rate`).
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Coordinate of the score vector.** `(scoreVec M ω).ofLp j = scoreCoord M j ω`. -/
theorem scoreVec_ofLp (M : GLMExpFamily n d μ) (ω : Ω) (j : Fin d) :
    (scoreVec M ω).ofLp j = scoreCoord M j ω := by
  simp only [scoreVec, WithLp.ofLp_toLp]

/-! ## Mean-zero of the score coordinate

`scoreCoord M j` is centered (`∫ scoreCoord M j = 0`), which lets us rewrite the two-sided
sub-Gaussian tail `μ {t < |X − ∫X|}` directly as a tail on `|scoreCoord M j|`. We re-derive the
mean identity `∫ yᵢ = ψ'(ηᵢ)` from the constitutive MGF identity `M.hmgf` (the same argument as in
`ScoreSubGaussian.lean`, whose pieces are private there). -/

/-- Integrability of `exp(s·yᵢ)` for every `s`, from the constitutive MGF identity. -/
private lemma y_exp_integrable (M : GLMExpFamily n d μ) (i : Fin n) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * M.y i ω)) μ := by
  by_contra hni
  have h0 := mgf_undef hni
  rw [M.hmgf i s] at h0
  exact (Real.exp_pos _).ne' h0

/-- The integrable-exponent set of `yᵢ` is all of `ℝ`. -/
private lemma y_integrableExpSet_univ (M : GLMExpFamily n d μ) (i : Fin n) :
    integrableExpSet (M.y i) μ = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact y_exp_integrable M i t

/-- The mean function identity `E[yᵢ] = ψ'(ηᵢ)`. -/
private lemma y_mean (M : GLMExpFamily n d μ) (i : Fin n) :
    ∫ ω, M.y i ω ∂μ = M.ψ' (linPred M.X M.θstar i) := by
  set η := linPred M.X M.θstar i with hη
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (M.y i) μ) := by
    rw [y_integrableExpSet_univ M i, interior_univ]; exact Set.mem_univ 0
  rw [← deriv_mgf_zero hmem]
  have hmgf_eq : mgf (M.y i) μ = fun s => Real.exp (M.ψ (η + s) - M.ψ η) := by
    funext s; rw [M.hmgf i s, hη]
  rw [hmgf_eq]
  have hinner : HasDerivAt (fun s => M.ψ (η + s) - M.ψ η) (M.ψ' η) 0 := by
    have h1 : HasDerivAt (fun s => M.ψ (η + s)) (M.ψ' η) 0 := by
      have := (M.hψ' (η + 0)).comp 0 ((hasDerivAt_id 0).const_add η)
      simpa using this
    simpa using h1.sub_const (M.ψ η)
  have hderiv : HasDerivAt (fun s => Real.exp (M.ψ (η + s) - M.ψ η)) (M.ψ' η) 0 := by
    simpa using hinner.exp
  exact hderiv.deriv

/-- **Mean-zero of the score coordinate.** `∫ scoreCoord M j = 0`, since each per-term variable
`Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is centered (`E[yᵢ] = ψ'(ηᵢ)`). -/
private lemma scoreCoord_integral_zero (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (j : Fin d) : ∫ ω, scoreCoord M j ω ∂μ = 0 := by
  set V : Fin n → Ω → ℝ :=
    fun i ω => (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j with hV
  have hV_sg : ∀ i, HasSubgaussianMGF (V i) ⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ μ :=
    fun i => score_term_hasSubgaussianMGF M i j
  have hVi : ∀ i, ∫ ω, V i ω ∂μ = 0 := by
    intro i
    have hyi : Integrable (M.y i) μ :=
      integrable_of_mem_interior_integrableExpSet (by
        rw [y_integrableExpSet_univ M i, interior_univ]; exact Set.mem_univ 0)
    have hrw : (fun ω => V i ω)
        = fun ω => M.ψ' (linPred M.X M.θstar i) * M.X i j - M.X i j * M.y i ω := by
      funext ω; simp only [hV]; ring
    rw [show (∫ ω, V i ω ∂μ)
          = ∫ ω, (M.ψ' (linPred M.X M.θstar i) * M.X i j - M.X i j * M.y i ω) ∂μ from by
        rw [hrw]]
    rw [integral_sub (integrable_const _) (hyi.const_mul _), integral_const,
        integral_const_mul, y_mean M i, probReal_univ, one_smul]
    ring
  have hsc_eq : scoreCoord M j = fun ω => (1 / (n : ℝ)) * ∑ i, V i ω := by
    funext ω; simp only [scoreCoord, hV]
  simp only [hsc_eq]
  rw [integral_const_mul,
      integral_finset_sum Finset.univ (fun i _ => (hV_sg i).integrable),
      Finset.sum_congr rfl (fun i _ => hVi i), Finset.sum_const_zero, mul_zero]

/-- **Union-bound tail on `‖scoreVec‖∞`** (Wainwright Cor 9.26 proof). For each coordinate the score is
sub-Gaussian with proxy `B²C²/n` (`score_coord_isSubGaussian`); a two-sided tail + union bound over the
`d` coordinates gives `P(‖scoreVec‖∞ > t) ≤ 2d·exp(−t²/(2·B²C²/n))`. (The `linfNorm_noise_tail` pattern.) -/
theorem score_linfNorm_tail (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    -- USER-INPUT: column normalization (G1); Wainwright §9.5 (G1).
    (C : ℝ) (hC : IsColumnNormalized M.X C)
    -- USER-INPUT: positive sample size; Wainwright Cor 9.26.
    (hn : 0 < n)
    -- USER-INPUT: positive variance proxy; needed for the tail (degenerate otherwise).
    (hσ : 0 < M.B ^ 2 * C ^ 2 / n)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | t < linfNorm (scoreVec M ω)} ≤
      ENNReal.ofReal (2 * d * Real.exp (-t ^ 2 / (2 * (M.B ^ 2 * C ^ 2 / n)))) := by
  -- ── Step 1: unfold linfNorm as sup over coordinates ───────────────────────────
  have hincl :
      {ω | t < linfNorm (scoreVec M ω)} ⊆
      ⋃ j : Fin d, {ω | t < |(scoreVec M ω).ofLp j|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    unfold linfNorm at hω
    rcases isEmpty_or_nonempty (Fin d) with hd0 | hne
    · have hval : ⨆ j : Fin d, |(scoreVec M ω).ofLp j| = 0 := by
        haveI := hd0
        change sSup (Set.range (fun j : Fin d => |(scoreVec M ω).ofLp j|)) = 0
        rw [Set.range_eq_empty_iff.mpr hd0, Real.sSup_empty]
      exact absurd (hval ▸ hω) (not_lt.mpr ht)
    · haveI := hne
      exact (lt_ciSup_iff (Set.finite_range _).bddAbove).mp hω
  -- ── Step 2: per-coordinate sub-Gaussian tail bound ────────────────────────────
  have hcol_sg : ∀ j : Fin d,
      IsSubGaussian (scoreCoord M j) ⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ μ :=
    fun j => score_coord_isSubGaussian M C hC hn j
  have hcol_tail : ∀ j : Fin d,
      μ {ω | t < |(scoreVec M ω).ofLp j|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (M.B ^ 2 * C ^ 2 / n)))) := by
    intro j
    have hm : ∫ x, scoreCoord M j x ∂μ = 0 := scoreCoord_integral_zero M j
    have hset : {ω | t < |(scoreVec M ω).ofLp j|} =
        {ω | t < |scoreCoord M j ω - ∫ x, scoreCoord M j x ∂μ|} := by
      ext ω; simp only [Set.mem_setOf_eq, scoreVec_ofLp, hm, sub_zero]
    rw [hset]
    simpa only [NNReal.coe_mk] using (hcol_sg j).measure_abs_sub_integral_lt_le ht
  -- ── Step 3: union bound over the d coordinates ────────────────────────────────
  calc μ {ω | t < linfNorm (scoreVec M ω)}
      ≤ μ (⋃ j : Fin d, {ω | t < |(scoreVec M ω).ofLp j|}) := measure_mono hincl
    _ ≤ ∑' j : Fin d, μ {ω | t < |(scoreVec M ω).ofLp j|} := measure_iUnion_le _
    _ = ∑ j : Fin d, μ {ω | t < |(scoreVec M ω).ofLp j|} := tsum_fintype _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (M.B ^ 2 * C ^ 2 / n)))) :=
          Finset.sum_le_sum fun j _ => hcol_tail j
    _ = ENNReal.ofReal (2 * d * Real.exp (-t ^ 2 / (2 * (M.B ^ 2 * C ^ 2 / n)))) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast (n := d),
              ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; ring

/-- **High-probability good event** (Wainwright Cor 9.26). With `λ = 4BC{√(log d/n) + δ}` (or larger),
`P(‖scoreVec‖∞ ≤ λ/2) ≥ 1 − 2·exp(−2nδ²)`. Setting `t = λ/2` in `score_linfNorm_tail`, the bound
`2d·exp(−nt²/(2B²C²))` simplifies to `2·exp(−2nδ²)` via `(a+b)² ≥ a²+b²` and `d ≥ 1`. -/
theorem good_event_highProb (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : IsColumnNormalized M.X C)
    -- USER-INPUT: positive sample size; Wainwright Cor 9.26.
    (hn : 0 < n)
    -- USER-INPUT: `d ≥ 1` (for `log d ≥ 0` and the union bound); Wainwright Cor 9.26.
    (hd : 0 < d)
    -- USER-INPUT: confidence offset `δ ∈ (0,1)`; Wainwright Cor 9.26.
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    -- USER-INPUT: positive cumulant/normalization constants `B, C`; Wainwright §9.5 (G1/G2).
    (hB : 0 < M.B) (hCpos : 0 < C)
    (lam : ℝ)
    -- USER-INPUT: tuning `λ ≥ 4BC{√(log d/n) + δ}`; Wainwright Cor 9.26.
    (hlam : 4 * M.B * C * (Real.sqrt (Real.log d / n) + δ) ≤ lam) :
    ENNReal.ofReal (1 - 2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)) ≤
      μ {ω | linfNorm (scoreVec M ω) ≤ lam / 2} := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
