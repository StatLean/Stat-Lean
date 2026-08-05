import StatLean.TimeSeries.Process.LinearProcess
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul

/-!
# Partial autocorrelation (FY §2.2.3, Definition 2.6, Proposition 2.3, Theorem 2.9)

The PACF via linear-regression residuals: for `k ≥ 2`,
`π(k) = Corr(R_{1|2..k}, R_{k+1|2..k})` where `R_{j|2..k}` is the residual of the best
linear approximation of `X_j` by `(X_2, …, X_k)` (FY Definition 2.6, eq. (2.28));
`π(1) = ρ(1)`. We take the **normal-equation coefficient vector** `Σ⁻¹γ` (with Mathlib's
junk-total `Matrix.inv`) as the regression coefficients — under the invertibility
hypothesis this *is* the arg-min of eq. (2.28), which we record as a lemma rather than a
definition. Main results:

* **Proposition 2.3(i)** (proof §2.7.2): the closed matrix formula FY eq. (2.29);
* **Proposition 2.3(ii)**: the PACF of a causal AR(p) vanishes beyond lag `p`;
* **Theorem 2.9** (proof §2.7.3): `π(k) = b_{kk}`, the last coefficient of the best
  linear AR(k) predictor (partitioned-inverse computation).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.3
(pp. 43–45: Definition 2.6, eqs. (2.28)–(2.29), Proposition 2.3, Theorem 2.9) and
§2.7.2–§2.7.3 (pp. 79–80). (`FY §2.2.3; §2.7.2–2.7.3`.)

**Proof formalization notes.**
* All objects are junk-total: `Matrix.inv` is the adjugate-based inverse (zero matrix
  when singular) and correlations divide by standard deviations (junk `0`); theorems
  carry the invertibility/nondegeneracy hypotheses the book leaves implicit (inventory
  flags).
* By stationarity everything is expressed through `acvf`; the covariance matrix of the
  window `(X_2, …, X_k)` is the Toeplitz matrix `Γ(i,j) = γ(i − j)`.
* FY's `R_{1|2..k}` vs `R_{k+1|2..k}` variance equality ("two-moment time
  reversibility") is the evenness of `γ` at the matrix level.

**Bibliographic comments.** Partial autocorrelation enters time-series identification
through Box & Jenkins (1970); the matrix formulas are classical multivariate regression
(cf. C. R. Rao, *Linear Statistical Inference*, 1973, p. 33 for the partitioned
inverse FY cites).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **Toeplitz autocovariance matrix** of a window of length `n`:
`(i, j) ↦ γ(i − j)`. -/
noncomputable def acvfToeplitz (X : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)

/-- The **normal-equation coefficients** for regressing `X_{t₀}` on the window
`(X_{w 0}, …, X_{w (n−1)})`: `Σ⁻¹ γ_vec`, junk-total via `Matrix.inv`. -/
noncomputable def linRegCoeffs (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ}
    (t0 : ℤ) (w : Fin n → ℤ) : Fin n → ℝ :=
  (Matrix.of fun i j => cov[X (w i), X (w j); μ])⁻¹ *ᵥ
    (fun i => cov[X t0, X (w i); μ])

/-- The **regression residual** of `X_{t₀}` on the window `w`. -/
noncomputable def linRegResidual (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ}
    (t0 : ℤ) (w : Fin n → ℤ) : Ω → ℝ :=
  fun ω => X t0 ω - ∑ i, linRegCoeffs X μ t0 w i * X (w i) ω

/-- The **partial autocorrelation function** (FY Definition 2.6): `π(1) = ρ(1)`, and for
`k ≥ 2` the correlation of the residuals of `X_1` and `X_{k+1}` regressed on
`(X_2, …, X_k)`. Junk-total (`Matrix.inv` + division conventions). -/
noncomputable def pacf (X : ℤ → Ω → ℝ) (μ : Measure Ω) (k : ℕ) : ℝ :=
  if k ≤ 1 then acf X μ 1
  else
    let w : Fin (k - 1) → ℤ := fun i => (i : ℕ) + 2
    let R1 := linRegResidual X μ 1 w
    let R2 := linRegResidual X μ ((k : ℤ) + 1) w
    cov[R1, R2; μ] / (Real.sqrt (variance R1 μ) * Real.sqrt (variance R2 μ))

/-- The normal-equation coefficients minimize the mean-squared prediction error
(FY eq. (2.28)) — the arg-min property, under invertibility of the window covariance
matrix (the book's implicit hypothesis, inventory flag). -/
theorem linRegCoeffs_isMinOn [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    -- USER-INPUT: nondegenerate window covariance; implicit in FY eq. (2.28)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det)
    (β : Fin n → ℝ) :
    variance (linRegResidual X μ t0 w) μ ≤
      variance (fun ω => X t0 ω - ∑ i, β i * X (w i) ω) μ := by
  sorry

/-- **Proposition 2.3(i)** (FY eq. (2.29); proof §2.7.2): the closed formula
`π(k) = (γ(k) − cᵀΣ⁻¹c̃) / (γ(0) − c̃ᵀΣ⁻¹c̃)` in Toeplitz form, under invertibility of
the inner-window covariance matrix. -/
theorem pacf_eq_matrix_formula [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {k : ℕ} (hk : 2 ≤ k)
    (hinv : IsUnit (Matrix.of fun i j : Fin (k - 1) =>
      cov[X (((i : ℕ) + 2 : ℕ) : ℤ), X (((j : ℕ) + 2 : ℕ) : ℤ); μ]).det)
    -- USER-INPUT: nondegenerate residual variances; implicit in FY Def 2.6
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) + 2 : ℤ))) μ) :
    pacf X μ k =
      (acvf X μ k - ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        acvf X μ ((k : ℤ) + 1 - ((i : ℕ) + 2)) *
          (Matrix.of fun i j : Fin (k - 1) =>
            acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))⁻¹ i j *
          acvf X μ (((j : ℕ) + 2 : ℤ) - 1)) /
      (acvf X μ 0 - ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        acvf X μ (1 - ((i : ℕ) + 2)) *
          (Matrix.of fun i j : Fin (k - 1) =>
            acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))⁻¹ i j *
          acvf X μ (((j : ℕ) + 2 : ℤ) - 1)) := by
  sorry

/-- **Theorem 2.9** (FY §2.2.3; proof §2.7.3, partitioned inverse): `π(k)` equals the
last coefficient of the best linear AR(k) predictor of `X_t` from
`(X_{t−1}, …, X_{t−k})`. -/
theorem pacf_eq_last_arCoeff [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) {k : ℕ} (hk : 1 ≤ k)
    (hinv : IsUnit (acvfToeplitz X μ k).det)
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) + 2 : ℤ))) μ) :
    pacf X μ k = linRegCoeffs X μ (k : ℤ)
      (fun i : Fin k => (k : ℤ) - 1 - (i : ℕ)) ⟨k - 1, by omega⟩ := by
  sorry

/-- **Proposition 2.3(ii)**: the PACF of a causal AR(p) process vanishes beyond lag
`p` (from Theorem 2.9 and the Yule–Walker structure: the best AR(k) predictor for
`k > p` uses only the first `p` coefficients). -/
theorem pacf_eq_zero_of_isAR [IsProbabilityMeasure μ] {p : ℕ} {b : Fin p → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b σ2 X ε μ) (hstat : IsStationary X μ)
    -- USER-INPUT: causality, as an explicit MA(∞) representation; FY Prop 2.3(ii)
    {ψ : ℕ → ℝ} (hψ : Summable fun n => |ψ n|) (hlin : IsLinearProcessOf ψ X ε μ)
    {k : ℕ}
    -- USER-INPUT: lag beyond the AR order; FY Prop 2.3(ii)
    (hk : p < k)
    (hinv : IsUnit (acvfToeplitz X μ k).det)
    (hpos : 0 < variance (linRegResidual X μ 1
      (fun i : Fin (k - 1) => ((i : ℕ) + 2 : ℤ))) μ) :
    pacf X μ k = 0 := by
  sorry

end StatLean.TimeSeries
