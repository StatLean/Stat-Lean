import StatLean.TimeSeries.ARMA.ScoreAnalysis
import StatLean.TimeSeries.Process.SampleACF

/-!
# Diagnostic checking of fitted ARMA models (FY §3.5)

* **Standardized residuals** (FY eq. (3.29)): the fitted-model residuals scaled by the
  estimated innovation standard deviation (`standardizedResiduals`; finite-sample
  object, defined through the AR(∞) inversion `armaPi` truncated to the sample);
* the **residual correlogram validity** claim (FY §3.5.2): for a correctly specified
  model with `√T`-consistent parameter estimates, the residual sample ACF at a fixed
  lag admits the same `±1.96/√T` bands as white noise — recorded as a literature
  DEBT at the granularity FY asserts it ("approximate validity from
  √T-consistency"; the exact Box–Pierce correction is cited only).

FY §3.5.3's formal whiteness tests live in ch. 7 (outside the current scope); no
portmanteau statistic appears in ch. 3, so none is stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.5,
eq. (3.29) (pp. 110–113). (`FY §3.5`.)

**Bibliographic comments.** Residual correlogram bands: Box & Jenkins (1970) §8.2;
the residual-ACF distribution correction is Box & Pierce (1970), refined by
Ljung & Box (1978) — both cited by FY without statements.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- **Truncated sample residuals** of a fitted ARMA model (FY eq. (3.29) numerators):
`ε̂_t = Σ_{j<t} π_j(b̂, â) x_{t−j}` (the AR(∞) inversion truncated at the sample
start; `t` is 0-based over the data vector). -/
noncomputable def sampleResiduals {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : ℝ :=
  ∑ j ∈ Finset.range ((t : ℕ) + 1),
    armaPi b a j * x ⟨(t : ℕ) - j, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩

/-- **Standardized residuals** (FY eq. (3.29)): residuals scaled by the plugged-in
innovation standard deviation `σ̂ = √(S/T)` (junk when `S ≤ 0`). -/
noncomputable def standardizedResiduals {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : ℝ :=
  sampleResiduals b a x t / Real.sqrt (armaProfileS b a x / T)

/-! ### Sanity checks on the finite-sample residual definitions

Three consistency facts that exercise `sampleResiduals`/`standardizedResiduals` on
concrete data: the leading residual is the leading observation (`π₀ = 1`), the AR(1)
residual is the explicit one-step prediction error `x_t − b₁ x_{t−1}`, and the
standardization really removes the scale of the data. -/

private lemma coeff_arPoly_aux {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then 1 else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]

private lemma coeff_maPoly_zero_aux {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- `π₀ = 1`: the AR(∞) inversion is normalized, since `b(0) = a(0) = 1`. -/
private lemma armaPi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) : armaPi b a 0 = 1 := by
  have ha : PowerSeries.constantCoeff (R := ℝ) ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
      = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_maPoly_zero_aux]
  have hb : PowerSeries.constantCoeff (R := ℝ) ((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
      = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_arPoly_aux]
    simp
  unfold armaPi
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_inv, ha, hb]
  norm_num

/-- **Sanity check 1**: the truncated residual at the sample start is the first
observation itself (nothing is available to predict it with). -/
private lemma sampleResiduals_at_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) (h0 : 0 < T) :
    sampleResiduals b a x ⟨0, h0⟩ = x ⟨0, h0⟩ := by
  simp [sampleResiduals, armaPi_zero]

/-- With no MA part the inversion coefficients are just the AR polynomial's. -/
private lemma armaPi_ma_nil {p : ℕ} (b : Fin p → ℝ) (n : ℕ) :
    armaPi b (Fin.elim0 : Fin 0 → ℝ) n = (arPoly b).coeff n := by
  have h : (maPoly (Fin.elim0 : Fin 0 → ℝ)) = 1 := by simp [maPoly]
  unfold armaPi
  rw [h]
  simp [Polynomial.coeff_coe]

/-- **Sanity check 2**: for a realized AR(1) sample the truncated residual is the
explicit one-step prediction error `ε̂_t = x_t − b₁ x_{t−1}` (the sum in
`sampleResiduals` collapses to its first two terms because `π_j = 0` for `j ≥ 2`). -/
private lemma sampleResiduals_ar_one {T : ℕ} (b : Fin 1 → ℝ) (x : Fin T → ℝ)
    (t : Fin T) (ht : 1 ≤ (t : ℕ)) :
    sampleResiduals b (Fin.elim0 : Fin 0 → ℝ) x t
      = x t - b 0 * x ⟨(t : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ := by
  have hsub : Finset.range 2 ⊆ Finset.range ((t : ℕ) + 1) := fun y hy =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega)
  unfold sampleResiduals
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, armaPi_ma_nil, armaPi_ma_nil,
      coeff_arPoly_aux, coeff_arPoly_aux]
    simp only [Fin.isValue]
    norm_num
    ring
  · intro j _ hj
    have h2 : 2 ≤ j := by simpa using hj
    rw [armaPi_ma_nil, coeff_arPoly_aux]
    simp [show j ≠ 0 by omega, show j ≠ 1 by omega]

private lemma sampleResiduals_const_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (c : ℝ) (x : Fin T → ℝ) (t : Fin T) :
    sampleResiduals b a (fun i => c * x i) t = c * sampleResiduals b a x t := by
  unfold sampleResiduals
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma armaProfileS_const_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (c : ℝ) (x : Fin T → ℝ) :
    armaProfileS b a (fun i => c * x i) = c ^ 2 * armaProfileS b a x := by
  unfold armaProfileS
  have h : (fun i => c * x i) = c • x := by funext i; simp
  rw [h, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul]
  ring

/-- **Sanity check 3**: the standardization does its job — rescaling the data by a
positive constant leaves the standardized residuals unchanged (the numerator scales by
`c`, the plugged-in `σ̂ = √(S/T)` by `c` as well, since `S` is quadratic). -/
private lemma standardizedResiduals_const_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} {c : ℝ} (hc : 0 < c) (x : Fin T → ℝ) (t : Fin T) :
    standardizedResiduals b a (fun i => c * x i) t = standardizedResiduals b a x t := by
  have hs : Real.sqrt (c ^ 2 * armaProfileS b a x / T)
      = c * Real.sqrt (armaProfileS b a x / T) := by
    rw [mul_div_assoc, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  unfold standardizedResiduals
  rw [sampleResiduals_const_mul, armaProfileS_const_mul, hs,
    mul_div_mul_left _ _ (ne_of_gt hc)]

/-- **DEBT (FY §3.5.2; Box–Jenkins folklore made precise by Box–Pierce 1970)**: for a
correctly specified stationary causal invertible ARMA with iid noise and any
`√T`-consistent estimator sequence, the lag-`k` sample ACF of the fitted residuals is
asymptotically `N(0, 1)` after `√T`-scaling — the basis of the `±1.96/√T` residual
correlogram bands. (The exact Box–Pierce variance deflation at small lags is a
strictly finer statement, cited only.) -/
theorem residual_acf_asymptotically_standard_debt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)) (hθmeas : ∀ T, Measurable (θ T))
    -- USER-INPUT: √T-consistency of the fitted parameters; FY §3.5.2
    (hcons : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ =>
      (μ {ω | δ ≤ Real.sqrt T * dist (θ T ω) (b0, a0)}).toReal) atTop (𝓝 0))
    {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * sampleACF
          (fun t : Fin T => sampleResiduals (θ T ω).1 (θ T ω).2
            (fun s : Fin T => X (((s : ℕ) : ℤ) + 1) ω) t) k) u)
      atTop (𝓝 (charFun (gaussianReal 0 1) u)) := by
  sorry

end StatLean.TimeSeries
