import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds
import StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.Increments
import StatLean.NonparametricStatistics.ForMathlib.MaxExpSquare
import StatLean.NonparametricStatistics.ForMathlib.GaussianExpSq

/-!
# Sup-norm control of the stochastic term of the local polynomial estimator

Under i.i.d. centered Gaussian noise and a Lipschitz boxed kernel, the stochastic component
of LP(`ℓ`) satisfies
$$ \mathbb E\Bigl[\ \sup_{t\in[0,1]}\Bigl|\sum_i \xi_i\,W^*_i(t)\Bigr|^2\Bigr]
   \;\le\; C\,\frac{\sigma_\xi^2\,\log n}{n h}, $$
with `C = C(ℓ, K_max, λ₀, a₀, L_K)` — the `log n` being the price of the supremum.

**Proof formalization notes.** Discretize `[0,1]` on the grid `t_j = j/M`, `M = n⁴`:

1. *Grid maximum.* At each grid point, `∑ᵢ ξᵢW*ᵢ(t_j) = U(0)ᵀB_{t_j}⁻¹·η_j/√(nh)·…` where the
   coordinates of `η_j = (nh)^{-1/2}∑ᵢ ξᵢU(zᵢ)K(zᵢ)` are *linear combinations of i.i.d.
   Gaussians*, hence Gaussian with variance `≤ 2a₀K²_max·σ_ξ²`
   (`hasLaw_sum_mul_gaussianReal` + the design density bound). The inverse bound converts
   `|∑ξW*| ≤ ‖η_j‖·…/λ₀·(nh)^{-1/2}`, and `lintegral_iSup_normSq_gaussian_le` gives
   `E max_j ‖η_j‖² ≲ (ℓ+1)·vmax·log(√2·M(ℓ+1)) = O(log n)`.
2. *Increments.* Between grid points, `∑ᵢ|W*ᵢ(t) − W*ᵢ(t_j)| ≤ C_L·|t−t_j|/h³`
   (`lp_weight_lipschitz_sum`, from `SupNorm/Increments.lean`), so the continuum supremum
   exceeds the grid maximum by at most `max_i|ξ_i|·C_L·n^{-4}/h³`, whose second moment is
   `O(σ_ξ²·log n·n^{-8}/h⁶) = o(σ_ξ²·log n/(nh))` for `h ≥ 1/(2n)`.

The constant is existential with the stated dependence (by binder position before the
quantifiers over `n`, the design, the noise, and the sample space).

**Bibliographic comments.** The discretize-and-bound-the-maximum route to sup-norm rates is
classical; cf. C. J. Stone, *Ann. Statist.* **10** (1982), 1040–1053, and W. Härdle,
*Applied Nonparametric Regression* (Cambridge, 1990).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- ℓ²-sum of local polynomial weights: `∑ᵢ Wᵢ(s)² ≤ (C*)²/(nh)`. -/
private lemma lp_sum_weight_sq_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {Kmax lam0 a₀ h : ℝ}
    {ℓ : ℕ} (hn : 0 < n) (hh : 0 < h) (hhl : 1 / (2 * (n : ℝ)) ≤ h) (hlam : 0 < lam0)
    (ha₀ : 0 ≤ a₀) (heig : DesignEigenvalueLB xdat K h ℓ lam0) (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, (lpWeight xdat K h ℓ s i) ^ 2 ≤ (lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hC : (0 : ℝ) ≤ lpWeightConst Kmax lam0 a₀ := by
    unfold lpWeightConst
    exact le_trans (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le) (le_max_left _ _)
  have hper : ∀ i, (lpWeight xdat K h ℓ s i) ^ 2
      ≤ lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * |lpWeight xdat K h ℓ s i| := by
    intro i
    have habs := lp_weight_abs_le hn hh hlam ha₀ heig hbox hs i
    have h1 : (lpWeight xdat K h ℓ s i) ^ 2
        = |lpWeight xdat K h ℓ s i| * |lpWeight xdat K h ℓ s i| := by rw [← sq_abs]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  calc ∑ i, (lpWeight xdat K h ℓ s i) ^ 2
      ≤ ∑ i, lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * |lpWeight xdat K h ℓ s i| :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * ∑ i, |lpWeight xdat K h ℓ s i| := by
        rw [← Finset.mul_sum]
    _ ≤ lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) * lpWeightConst Kmax lam0 a₀ :=
        mul_le_mul_of_nonneg_left (lp_weight_sum_abs_le hn hhl hlam ha₀ heig hbox hdens hs)
          (div_nonneg hC hnh.le)
    _ = (lpWeightConst Kmax lam0 a₀) ^ 2 / ((n : ℝ) * h) := by rw [div_mul_eq_mul_div, ← pow_two]

/-- Every point of `[0,1]` lies within `1/M` of a grid point `j/M`, `j ≤ M`. -/
private lemma exists_grid_near {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : Fin (M + 1), |t - (j : ℝ) / M| ≤ 1 / M := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have htM : 0 ≤ t * M := mul_nonneg ht.1 hMr.le
  have hle : t * (M : ℝ) ≤ (M : ℝ) := by nlinarith [ht.2, hMr.le]
  have hjle : Nat.floor (t * M) ≤ M := by
    calc Nat.floor (t * M) ≤ Nat.floor ((M : ℝ)) := Nat.floor_le_floor hle
      _ = M := Nat.floor_natCast M
  refine ⟨⟨Nat.floor (t * M), Nat.lt_succ_iff.mpr hjle⟩, ?_⟩
  have hflle : (Nat.floor (t * M) : ℝ) ≤ t * M := Nat.floor_le htM
  have hltfl : t * M < Nat.floor (t * M) + 1 := Nat.lt_floor_add_one _
  have hval : ((⟨Nat.floor (t * M), Nat.lt_succ_iff.mpr hjle⟩ : Fin (M + 1)) : ℝ)
      = (Nat.floor (t * M) : ℝ) := rfl
  have he : t - (Nat.floor (t * M) : ℝ) / M = (t * M - Nat.floor (t * M)) / M := by
    field_simp
  have habs1 : |t * M - (Nat.floor (t * M) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [hflle, hltfl]
  rw [hval, he, abs_div, abs_of_pos hMr, div_le_div_iff₀ hMr hMr]
  exact mul_le_mul_of_nonneg_right habs1 hMr.le

/-- `log(√2·(n⁴+1)) ≤ 6·log n` for `n ≥ 2` (the price of the `n⁴`-point grid). -/
private lemma log_sqrt2_grid_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.sqrt 2 * ((n : ℝ) ^ 4 + 1)) ≤ 6 * Real.log n := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num); rwa [h4] at this
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : (1 : ℕ) ≤ n ^ 4 := Nat.one_le_pow 4 n (by omega)
    exact_mod_cast this
  have hbound : Real.sqrt 2 * ((n : ℝ) ^ 4 + 1) ≤ (n : ℝ) ^ 6 := by
    have h1 : (n : ℝ) ^ 4 + 1 ≤ 2 * (n : ℝ) ^ 4 := by nlinarith [hn4]
    calc Real.sqrt 2 * ((n : ℝ) ^ 4 + 1) ≤ 2 * (2 * (n : ℝ) ^ 4) := by
          apply mul_le_mul hs2 h1 (by positivity) (by norm_num)
      _ = 4 * (n : ℝ) ^ 4 := by ring
      _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 4 := by
          have h4n : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnr]
          nlinarith [h4n, pow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith) 4]
      _ = (n : ℝ) ^ 6 := by ring
  calc Real.log (Real.sqrt 2 * ((n : ℝ) ^ 4 + 1))
      ≤ Real.log ((n : ℝ) ^ 6) := Real.log_le_log (by positivity) hbound
    _ = 6 * Real.log n := by rw [Real.log_pow]; push_cast; ring

/-- Second moment of a centered Gaussian as a lower Lebesgue integral: `∫⁻ x², d𝒩(0,v) = v`. -/
private lemma gaussian_lintegral_sq (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (v : ℝ) := by
  have hint : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
    have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simpa [integral_id_gaussianReal] using hv
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall (fun x => sq_nonneg x)),
    hint]

/-- **Sup-norm stochastic bound**: there is `C = C(ℓ, K_max, λ₀, a₀, L_K)` such that under
the standing design assumptions, a Lipschitz boxed kernel, and i.i.d. `N(0, v)` noise,
`E[(sup_{t∈[0,1]} |∑ᵢ ξᵢ·W*ᵢ(t)|)²] ≤ C·v·log n/(n·h)` for all `n ≥ 2`,
`1/(2n) ≤ h ≤ 1`. -/
theorem lp_supnorm_stochastic_le {ℓ : ℕ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ}
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n → ∀ {h : ℝ}, 1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h ℓ lam0 → DesignDensityBound xdat a₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ) (v : ℝ≥0),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) →
        ∫⁻ ω, ENNReal.ofReal
            ((⨆ t : Set.Icc (0 : ℝ) 1, |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
  sorry

end StatLean.NonparametricStatistics
