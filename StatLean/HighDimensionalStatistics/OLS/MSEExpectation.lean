import StatLean.HighDimensionalStatistics.LinearModel.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Expected MSE of OLS — Lu-BDA §5 `thm:mse-ols`, expectation half

Main result `mse_ols_expectation_le`: for `Y ω = X β* + ε ω` with noise `ε` having
independent mean-0 coordinates each sub-Gaussian proxy `σ²`, every OLS estimator `βhat`
satisfies  `E[MSE(Xβ̂, Xβ*)] ≤ σ² · rank(X) / n`.

Proof outline:
1. OLS minimizer ⟹ `Xβ̂ = P_C(Y)` (orthogonal projection onto column space `C = C(X)`).
2. Prediction error `Xβ̂ − Xβ* = P_C(ε)` (linearity + `Xβ* ∈ C`).
3. Parseval: `‖P_C(ε)‖² = ∑_{k<r} ⟪e_k, ε⟫²` (ONB `{e_k}` of `C`).
4. Each `⟪e_k, ε⟫ = ∑_i (e_k)_i · ε_i` is sub-Gaussian proxy `σ²`
   (independent linear combination, unit-vector coefficient).
5. Named sorry (ESCALATE): `E[Z²] ≤ σ²` for mean-0 `HasSubgaussianMGF Z σ² μ`.
6. Sum: `E[MSE] ≤ (1/n) · r · σ² = σ² · r / n`.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal NNReal

namespace StatLean.HighDimensionalStatistics
open StatLean.ConcentrationInequalities

variable {n d : ℕ}

/-! ### Named sorry — variance bound for sub-Gaussian variables (Mathlib gap) -/

/-- **Variance ≤ proxy for mean-0 sub-Gaussian — ESCALATE.**

For a mean-0 `HasSubgaussianMGF X σ2 μ`, the second moment satisfies `E[X²] ≤ σ2`.

**Proof sketch:** the MGF `M(t) = E[exp(tX)] ≤ exp(σ2·t²/2)` for all t, and `M(0) = 1`,
`M'(0) = E[X] = 0`. A second-order comparison gives `M''(0) = E[X²] ≤ σ2`.
Mathlib has `HasSubgaussianMGF.cgf_le` (the log-MGF bound) and `MGFAnalytic` (analyticity),
but lacks the comparison `iteratedDeriv 2 (mgf X μ) 0 ≤ σ2`.
**ESCALATE:** upstream PR should add `HasSubgaussianMGF.integral_sq_le`. -/
private lemma hasSubgaussianMGF_integral_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ2 : ℝ≥0}
    (h : HasSubgaussianMGF X σ2 μ) (hX_mean : ∫ ω, X ω ∂μ = 0) :
    ∫ ω, X ω ^ 2 ∂μ ≤ σ2 := by
  sorry

/-! ### Helper: orthogonality of residual from the OLS first-order condition -/

/-- The OLS residual `Y − Xβ̂` is orthogonal to every element of `columnSpace X`.
This is the standard first-order (gradient) condition for a least-squares minimiser. -/
private lemma ols_residual_orthogonal
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d))
    (hols : IsOLSEstimator X Y βhat)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ columnSpace X) :
    ⟪Y - designMap X βhat, w⟫_ℝ = 0 := by
  obtain ⟨γ, rfl⟩ := hw
  -- Abbreviate: r = residual, v = Xγ, c = ⟪r, v⟫, s = ‖v‖².
  set r := Y - designMap X βhat with hr_def
  set v := designMap X γ with hv_def
  set c := ⟪r, v⟫_ℝ
  set s := ‖v‖ ^ 2
  -- First-order condition: perturbing βhat by tγ gives a competitor.
  -- ‖Y − X(βhat + tγ)‖² ≥ ‖Y − Xβ̂‖², i.e., 0 ≤ −2tc + t²s for all t.
  have h0 : ∀ t : ℝ, 0 ≤ t ^ 2 * s - 2 * t * c := by
    intro t
    have hcomp := hols (βhat + t • γ)
    simp only [map_add, map_smul] at hcomp
    have expand : ‖Y - (designMap X βhat + t • v)‖ ^ 2
        = ‖r‖ ^ 2 - 2 * t * c + t ^ 2 * s := by
      simp only [hr_def, hv_def, s, c]
      have : Y - (designMap X βhat + t • designMap X γ) = r - t • v := by
        simp [r, v]; ring
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          ← Real.sq_abs, sq (|t|), ← mul_assoc]
      ring
    linarith [expand ▸ hcomp]
  -- Specialise at t = c / (2 + s): obtain 0 ≤ −c²(4+s)/(2+s)², so c² ≤ 0, so c = 0.
  have hs_nn : 0 ≤ s := sq_nonneg _
  have h_spec := h0 (c / (2 + s))
  have heq : (c / (2 + s)) ^ 2 * s - 2 * (c / (2 + s)) * c
      = -(c ^ 2 * (4 + s)) / (2 + s) ^ 2 := by field_simp; ring
  rw [heq] at h_spec
  -- 0 ≤ -(c²(4+s)) / (2+s)² and (2+s)² > 0 imply c²(4+s) ≤ 0.
  have hnum_nn : 0 ≤ -(c ^ 2 * (4 + s)) := by
    rwa [le_div_iff (by positivity), mul_zero] at h_spec
  have hc_sq_le : c ^ 2 ≤ 0 := by nlinarith [sq_nonneg c]
  exact sq_eq_zero_iff.mp (le_antisymm hc_sq_le (sq_nonneg c))

/-! ### OLS prediction = orthogonal projection -/

/-- The OLS prediction `Xβ̂` equals the orthogonal projection of `Y` onto `columnSpace X`.
Follows from uniqueness of the orthogonal projection, characterised by orthogonality. -/
private lemma ols_pred_eq_proj
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d))
    (hols : IsOLSEstimator X Y βhat)
    [hC_proj : (columnSpace X).HasOrthogonalProjection] :
    (columnSpace X).starProjection Y = designMap X βhat :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self _ _)
    (fun w hw => ols_residual_orthogonal X Y βhat hols hw)

/-! ### designRank = finrank of columnSpace -/

private lemma designRank_eq_finrank_columnSpace (X : Matrix (Fin n) (Fin d) ℝ) :
    designRank X = Module.finrank ℝ ↥(columnSpace X) := by
  simp only [designRank, columnSpace, designMap]
  rw [Matrix.rank_eq_finrank_range_toLin X
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  congr 1
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-! ### Main theorem -/

/-- **Expected MSE of OLS — Lu-BDA §5 `thm:mse-ols`, expectation half.**

For `Y ω = X β* + ε ω` with noise `ε` having independent mean-0 coordinates each
sub-Gaussian proxy `σ²`, every OLS estimator `βhat` satisfies
  `E[MSE(Xβ̂, Xβ*)] ≤ σ² · rank(X) / n`.

**Hypotheses:**
- `hε_indep` (USER-INPUT; Lu-BDA §5 thm:mse-ols): joint independence of noise coordinates.
- `hε_meanz` (USER-INPUT; Lu-BDA §5 thm:mse-ols): mean-0 noise coordinates.
- `hε_subG` (USER-INPUT; Lu-BDA §5 thm:mse-ols): sub-Gaussian proxy σ² per coordinate.
- `hβ_ols` (USER-INPUT; Lu-BDA §5 thm:mse-ols): βhat ω is OLS for Y ω = Xβ* + ε ω.
- `hn` (LEAN-ONLY): `n > 0` for the (1/n) factor to be well-typed.

**One named sorry:** `hasSubgaussianMGF_integral_sq_le` (variance ≤ σ²); Mathlib gap. -/
theorem mse_ols_expectation_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    -- LEAN-ONLY: needed so (1/n : ℝ) is well-defined and the final bound is finite; no scope change
    (hn : 0 < n)
    {σ2 : ℝ≥0}
    {ε : Ω → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: noise coordinates are jointly independent; Lu-BDA §5 thm:mse-ols
    (hε_indep : iIndepFun (fun (i : Fin n) (ω : Ω) => (ε ω) i) μ)
    -- USER-INPUT: each noise coordinate has mean 0; Lu-BDA §5 thm:mse-ols
    (hε_meanz : ∀ i : Fin n, ∫ ω, (ε ω) i ∂μ = 0)
    -- USER-INPUT: each noise coordinate is sub-Gaussian proxy σ²; Lu-BDA §5 thm:mse-ols
    (hε_subG : ∀ i : Fin n, IsSubGaussian (fun ω => (ε ω) i) σ2 μ)
    -- USER-INPUT: true coefficient vector; Lu-BDA §5 thm:mse-ols
    (βstar : EuclideanSpace ℝ (Fin d))
    {βhat : Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: βhat ω minimises ‖Y ω − Xβ‖² over β; Lu-BDA §5 thm:mse-ols
    (hβ_ols : ∀ ω, IsOLSEstimator X (designMap X βstar + ε ω) (βhat ω)) :
    ∫ ω, mse X (βhat ω) βstar ∂μ ≤ ↑σ2 * ↑(designRank X) / ↑n := by
  -- Setup: column space C = range(X), finite-dimensional ⟹ complete ⟹ has orthogonal projection.
  let C := columnSpace X
  haveI hC_fd : FiniteDimensional ℝ ↥C := LinearMap.finiteDimensional_range _
  haveI hC_complete : CompleteSpace ↥C := inferInstance
  haveI hC_proj : C.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace C
  let r := Module.finrank ℝ ↥C
  -- Standard ONB for C, indexed by Fin r.
  let b : OrthonormalBasis (Fin r) ℝ ↥C := stdOrthonormalBasis ℝ ↥C
  -- Step 1: OLS prediction = orthogonal projection of Y ω onto C.
  have hpred : ∀ ω, C.starProjection (designMap X βstar + ε ω) = designMap X (βhat ω) :=
    fun ω => ols_pred_eq_proj X (designMap X βstar + ε ω) (βhat ω) (hβ_ols ω)
  -- Step 2: Prediction error = projection of noise (since Xβ* ∈ C is a fixed point).
  have hXβstar_mem : designMap X βstar ∈ C := LinearMap.mem_range_self _ _
  have hpred_err : ∀ ω,
      designMap X (βhat ω) - designMap X βstar = C.starProjection (ε ω) := by
    intro ω
    have hfix : C.starProjection (designMap X βstar) = designMap X βstar :=
      Submodule.starProjection_mem_subspace_eq_self ⟨designMap X βstar, hXβstar_mem⟩
    rw [← hpred ω, (C.starProjection).map_add, hfix]
    ring
  -- Step 3: MSE at ω = (1/n) · ‖P_C(ε ω)‖².
  have hmse_eq : ∀ ω,
      mse X (βhat ω) βstar = (1 / ↑n : ℝ) * ‖C.starProjection (ε ω)‖ ^ 2 := by
    intro ω; simp [mse, hpred_err ω]
  -- Step 4: Parseval identity in the subspace —
  --         ‖P_C(x)‖² = ∑_{k<r} ⟪(b k : E), x⟫².
  have hParseval : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖C.starProjection x‖ ^ 2
        = ∑ k : Fin r, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), x⟫_ℝ ^ 2 := by
    intro x
    -- Rewrite norm via the subtype: starProjection x = ↑(orthogonalProjection x)
    -- and the subtype norm equals the ambient norm.
    rw [Submodule.starProjection_apply, Submodule.norm_coe,
        ← b.sum_sq_inner_right (C.orthogonalProjection x)]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    -- ⟪b k, orthogonalProjection x⟫_{↥C} = ⟪(b k : E), x⟫_E
    exact Submodule.inner_orthogonalProjection_eq_of_mem_left (b k) x
  -- Step 5: Each inner product ⟪(b k : E), ε⟫ is sub-Gaussian with proxy σ².
  have hinner_subG : ∀ k : Fin r,
      HasSubgaussianMGF (fun ω => ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ) σ2 μ := by
    intro k
    -- Abbreviate the ambient unit vector e_k = ↑(b k).
    let e : EuclideanSpace ℝ (Fin n) := (b k : ↥C)
    -- Coordinate decomposition: ⟪e, ε ω⟫ = ∑_i e_i * (ε ω)_i.
    have hinner_sum : ∀ ω, ⟪e, ε ω⟫_ℝ = ∑ i : Fin n, e i * (ε ω) i := by
      intro ω
      -- PiLp.inner_apply + RCLike.inner_apply (⟪a,b⟫_ℝ = b * conj a = b * a for a b : ℝ)
      simp only [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    -- Each coordinate i: scaled noise e_i * (ε ω)_i is sub-Gaussian proxy ⟨e_i², _⟩ * σ2.
    have h_subG_i : ∀ i : Fin n,
        HasSubgaussianMGF (fun ω => e i * (ε ω) i) (⟨(e i) ^ 2, sq_nonneg _⟩ * σ2) μ := by
      intro i
      -- IsSubGaussian (ε · i) σ2 μ = HasSubgaussianMGF (fun ω => (ε ω) i - 0) σ2 μ
      have h_raw : HasSubgaussianMGF (fun ω => (ε ω) i) σ2 μ := by
        have := hε_subG i
        rwa [hε_meanz i, sub_zero] at this
      exact h_raw.const_mul (e i)
    -- Independence: scaling by constants preserves the iIndepFun structure.
    have h_indep_i : iIndepFun (fun i ω => e i * (ε ω) i) μ :=
      hε_indep.comp (fun i (x : ℝ) => e i * x)
        (fun i => measurable_const.mul measurable_id)
    -- Sum over all coordinates is sub-Gaussian with proxy ∑_i ⟨e_i², _⟩ * σ2.
    have hsum_subG : HasSubgaussianMGF (fun ω => ∑ i : Fin n, e i * (ε ω) i)
        (∑ i : Fin n, ⟨(e i) ^ 2, sq_nonneg _⟩ * σ2) μ :=
      HasSubgaussianMGF.sum_of_iIndepFun h_indep_i (fun i _ => h_subG_i i)
    -- The proxy collapses: ∑_i ⟨e_i², _⟩ * σ2 = σ2 because ‖e‖ = 1.
    have hproxy : ∑ i : Fin n, (⟨(e i) ^ 2, sq_nonneg _⟩ : ℝ≥0) * σ2 = σ2 := by
      -- Reduce to showing ∑_i ⟨e_i², _⟩ = 1 in ℝ≥0.
      have hsum1 : ∑ i : Fin n, (⟨(e i) ^ 2, sq_nonneg _⟩ : ℝ≥0) = 1 := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one]
        -- ∑_i (e i)² = ‖e‖² = ‖b k‖² = 1² = 1
        rw [← EuclideanSpace.real_norm_sq_eq e]
        have he_norm : ‖e‖ = 1 := by
          have hbk := b.orthonormal.1 k
          rwa [e, Submodule.norm_coe] at hbk
        rw [he_norm, one_pow]
      rw [← Finset.sum_mul, hsum1, one_mul]
    rw [hproxy] at hsum_subG
    exact hsum_subG.congr (ae_of_all _ fun ω => (hinner_sum ω).symm)
  -- Step 6: Mean of each inner product = 0 (from hε_meanz and linearity).
  have hinner_meanz : ∀ k : Fin r,
      ∫ ω, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ∂μ = 0 := by
    intro k
    let e : EuclideanSpace ℝ (Fin n) := (b k : ↥C)
    have hinner_sum : ∀ ω, ⟪e, ε ω⟫_ℝ = ∑ i : Fin n, e i * (ε ω) i := fun ω => by
      simp only [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have hint : ∀ i : Fin n, Integrable (fun ω => e i * (ε ω) i) μ := fun i => by
      apply Integrable.const_mul
      have h_int := (hε_subG i : HasSubgaussianMGF (fun ω => (ε ω) i - ∫ ω', (ε ω') i ∂μ) σ2 μ)
      rw [hε_meanz i, sub_zero] at h_int
      exact h_int.integrable
    rw [show (fun ω => ⟪e, ε ω⟫_ℝ) = fun ω => ∑ i : Fin n, e i * (ε ω) i
          from funext hinner_sum,
        integral_finset_sum Finset.univ (fun i _ => hint i)]
    apply Finset.sum_eq_zero; intro i _
    rw [integral_mul_left, hε_meanz i, mul_zero]
  -- Step 7: Apply variance bound: E[⟪e_k, ε⟫²] ≤ σ2.
  have hE_sq : ∀ k : Fin r,
      ∫ ω, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2 ∂μ ≤ σ2 :=
    fun k => hasSubgaussianMGF_integral_sq_le (hinner_subG k) (hinner_meanz k)
  -- Step 8: Assemble the bound E[MSE] ≤ (1/n) · r · σ2.
  have h_pointwise : ∀ ω, mse X (βhat ω) βstar =
      (1 / ↑n : ℝ) * ∑ k : Fin r,
        ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2 :=
    fun ω => (hmse_eq ω).trans (by rw [hParseval (ε ω)])
  have hint_inner_sq : ∀ k : Fin r,
      Integrable (fun ω => ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2) μ :=
    fun k => ((hinner_subG k).memLp 2).integrable_sq
  have hE_mse : ∫ ω, mse X (βhat ω) βstar ∂μ ≤ (1 / ↑n : ℝ) * (↑r * ↑σ2) := by
    rw [show (fun ω => mse X (βhat ω) βstar) =
          fun ω => (1 / ↑n : ℝ) * ∑ k : Fin r,
            ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2
          from funext h_pointwise,
        integral_const_mul,
        integral_finset_sum Finset.univ (fun k _ => hint_inner_sq k)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ k : Fin r, ∫ ω, ⟪((b k : ↥C) : EuclideanSpace ℝ (Fin n)), ε ω⟫_ℝ ^ 2 ∂μ
        ≤ ∑ k : Fin r, (σ2 : ℝ) := Finset.sum_le_sum (fun k _ => hE_sq k)
      _ = ↑r * ↑σ2 := by
            simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, nsmul_eq_mul]
  -- Step 9: Convert to σ2 · designRank / n.
  calc ∫ ω, mse X (βhat ω) βstar ∂μ
      ≤ (1 / ↑n : ℝ) * (↑r * ↑σ2) := hE_mse
    _ = ↑σ2 * ↑(designRank X) / ↑n := by
          rw [designRank_eq_finrank_columnSpace]; push_cast; ring

end StatLean.HighDimensionalStatistics
