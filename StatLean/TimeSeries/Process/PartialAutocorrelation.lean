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

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ProbabilityTheory Topology

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

/-! ### The regression toolkit

Bilinearity of the covariance against the window, the normal equations `Σα = c` supplied
by `Matrix.mul_nonsing_inv`, and the resulting orthogonality `R ⊥ X_{w l}` — the three
facts every result below runs on. -/

section Toolkit

variable {X : ℤ → Ω → ℝ}

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {Y Y' Z Z' : Ω → ℝ} (hY : Y =ᵐ[μ] Y') (hZ : Z =ᵐ[μ] Z') :
    cov[Y, Z; μ] = cov[Y', Z'; μ] := by
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  have hIZ : ∫ x, Z x ∂μ = ∫ x, Z' x ∂μ := integral_congr_ae hZ
  simp only [covariance, hIY, hIZ]
  exact integral_congr_ae (by filter_upwards [hY, hZ] with ω h1 h2 using by rw [h1, h2])

/-- Definitional unfolding of the residual. -/
private lemma linRegResidual_eq (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ} (t0 : ℤ)
    (w : Fin n → ℤ) :
    linRegResidual X μ t0 w
      = fun ω => X t0 ω - ∑ i, linRegCoeffs X μ t0 w i * X (w i) ω := rfl

/-- Entrywise form of the normal-equation coefficients. -/
private lemma linRegCoeffs_eq (X : ℤ → Ω → ℝ) (μ : Measure Ω) {n : ℕ} (t0 : ℤ)
    (w : Fin n → ℤ) (i : Fin n) :
    linRegCoeffs X μ t0 w i
      = ∑ j, (Matrix.of fun i j => cov[X (w i), X (w j); μ])⁻¹ i j
          * cov[X t0, X (w j); μ] := rfl

/-- Square-integrability of a linear combination of the window. -/
private lemma memLp_window (hstat : IsStationary X μ) {n : ℕ} (w : Fin n → ℤ)
    (c : Fin n → ℝ) : MemLp (fun ω => ∑ i, c i * X (w i) ω) 2 μ :=
  memLp_finset_sum _ fun i _ => (hstat.memLp (w i)).const_mul (c i)

/-- Square-integrability of the regression residual. -/
private lemma memLp_linRegResidual (hstat : IsStationary X μ) {n : ℕ} (t0 : ℤ)
    (w : Fin n → ℤ) : MemLp (linRegResidual X μ t0 w) 2 μ :=
  (hstat.memLp t0).sub (memLp_window hstat w _)

/-- Bilinear expansion of the residual covariance. -/
private lemma cov_linRegResidual_left [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    cov[linRegResidual X μ t0 w, Y; μ]
      = cov[X t0, Y; μ] - ∑ i, linRegCoeffs X μ t0 w i * cov[X (w i), Y; μ] := by
  rw [linRegResidual_eq,
    covariance_fun_sub_left (hstat.memLp t0) (memLp_window hstat w _) hY,
    covariance_fun_sum_left (fun i => (hstat.memLp (w i)).const_mul _) hY]
  simp_rw [covariance_const_mul_left]

/-- The **normal equations** `Σ α = c` (FY §2.7.2): the defining property of
`linRegCoeffs`, from `M * M⁻¹ = 1`. -/
private lemma linRegCoeffs_normalEq {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (l : Fin n) :
    ∑ j, cov[X (w l), X (w j); μ] * linRegCoeffs X μ t0 w j = cov[X t0, X (w l); μ] := by
  have h : (Matrix.of fun i j => cov[X (w i), X (w j); μ]) *ᵥ linRegCoeffs X μ t0 w
      = fun i => cov[X t0, X (w i); μ] := by
    rw [linRegCoeffs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec]
  simpa [Matrix.mulVec, dotProduct] using congrFun h l

/-- **Uniqueness** of the normal-equation solution under invertibility. -/
private lemma linRegCoeffs_eq_of_normalEq {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (b : Fin n → ℝ)
    (hb : ∀ l, ∑ j, cov[X (w l), X (w j); μ] * b j = cov[X t0, X (w l); μ]) :
    linRegCoeffs X μ t0 w = b := by
  have hM : (Matrix.of fun i j => cov[X (w i), X (w j); μ]) *ᵥ b
      = fun i => cov[X t0, X (w i); μ] := by
    funext l; simpa [Matrix.mulVec, dotProduct] using hb l
  rw [linRegCoeffs, ← hM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv,
    Matrix.one_mulVec]

/-- **Orthogonality** (FY eq. (2.70)): the residual is uncorrelated with every window
coordinate. -/
private lemma cov_linRegResidual_window [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (l : Fin n) :
    cov[linRegResidual X μ t0 w, X (w l); μ] = 0 := by
  rw [cov_linRegResidual_left hstat t0 w (hstat.memLp (w l))]
  have h2 : ∑ i, linRegCoeffs X μ t0 w i * cov[X (w i), X (w l); μ]
      = ∑ j, cov[X (w l), X (w j); μ] * linRegCoeffs X μ t0 w j :=
    Finset.sum_congr rfl fun i _ => by rw [covariance_comm]; ring
  rw [h2, linRegCoeffs_normalEq t0 w hinv l, sub_self]

/-- The residual is uncorrelated with every linear combination of the window. -/
private lemma cov_linRegResidual_windowSum [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) (c : Fin n → ℝ) :
    cov[linRegResidual X μ t0 w, fun ω => ∑ i, c i * X (w i) ω; μ] = 0 := by
  rw [covariance_fun_sum_right (fun i => (hstat.memLp (w i)).const_mul (c i))
    (memLp_linRegResidual hstat t0 w)]
  simp_rw [covariance_const_mul_right, cov_linRegResidual_window hstat t0 w hinv]
  simp

/-- The covariance of two residuals on a common window collapses onto the raw variable
(FY eq. (2.70)). -/
private lemma cov_linRegResidual_residual [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 t1 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    cov[linRegResidual X μ t0 w, linRegResidual X μ t1 w; μ]
      = cov[X t0, X t1; μ] - ∑ i, linRegCoeffs X μ t0 w i * cov[X (w i), X t1; μ] := by
  have h1 : cov[linRegResidual X μ t0 w, linRegResidual X μ t1 w; μ]
      = cov[linRegResidual X μ t0 w, X t1; μ] := by
    rw [linRegResidual_eq X μ t1 w,
      covariance_fun_sub_right (memLp_linRegResidual hstat t0 w) (hstat.memLp t1)
        (memLp_window hstat w _),
      cov_linRegResidual_windowSum hstat t0 w hinv, sub_zero]
  rw [h1, cov_linRegResidual_left hstat t0 w (hstat.memLp t1)]

/-- The residual covariance in autocovariance form. -/
private lemma cov_linRegResidual_residual_acvf [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {n : ℕ} (t0 t1 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    cov[linRegResidual X μ t0 w, linRegResidual X μ t1 w; μ]
      = acvf X μ (t0 - t1) - ∑ i, linRegCoeffs X μ t0 w i * acvf X μ (w i - t1) := by
  rw [cov_linRegResidual_residual hstat t0 t1 w hinv]
  simp_rw [hstat.cov_eq_acvf]

/-- The residual variance in autocovariance form. -/
private lemma variance_linRegResidual [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 : ℤ) (w : Fin n → ℤ)
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    variance (linRegResidual X μ t0 w) μ
      = acvf X μ 0 - ∑ i, linRegCoeffs X μ t0 w i * acvf X μ (w i - t0) := by
  rw [← covariance_self
      (memLp_linRegResidual hstat t0 w).aestronglyMeasurable.aemeasurable,
    cov_linRegResidual_residual_acvf hstat t0 t0 w hinv, sub_self]

/-- The coefficients are equivariant under a joint time shift and a relabelling of the
window: both leave every covariance entry unchanged. -/
private lemma linRegCoeffs_reindex_shift [IsProbabilityMeasure μ] (hstat : IsStationary X μ)
    {n : ℕ} (t0 s : ℤ) (w : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (hinv : IsUnit (Matrix.of fun i j => cov[X (w i), X (w j); μ]).det) :
    linRegCoeffs X μ (t0 + s) (fun i => w (σ i) + s)
      = fun i => linRegCoeffs X μ t0 w (σ i) := by
  have hcov : ∀ i j : Fin n,
      cov[X (w (σ i) + s), X (w (σ j) + s); μ] = cov[X (w (σ i)), X (w (σ j)); μ] := by
    intro i j
    rw [hstat.cov_eq_acvf, hstat.cov_eq_acvf]
    congr 1
    ring
  have hsub : (Matrix.of fun i j => cov[X (w (σ i) + s), X (w (σ j) + s); μ])
      = (Matrix.of fun i j => cov[X (w i), X (w j); μ]).submatrix σ σ := by
    ext i j; simpa using hcov i j
  have hinv' : IsUnit (Matrix.of fun i j => cov[X (w (σ i) + s), X (w (σ j) + s); μ]).det := by
    rw [hsub, Matrix.det_submatrix_equiv_self]; exact hinv
  refine linRegCoeffs_eq_of_normalEq _ _ hinv' _ fun l => ?_
  have hR : cov[X (t0 + s), X (w (σ l) + s); μ] = cov[X t0, X (w (σ l)); μ] := by
    rw [hstat.cov_eq_acvf, hstat.cov_eq_acvf]; congr 1; ring
  calc ∑ j, cov[X (w (σ l) + s), X (w (σ j) + s); μ] * linRegCoeffs X μ t0 w (σ j)
      = ∑ j, cov[X (w (σ l)), X (w (σ j)); μ] * linRegCoeffs X μ t0 w (σ j) :=
        Finset.sum_congr rfl fun j _ => by rw [hcov]
    _ = ∑ j, cov[X (w (σ l)), X (w j); μ] * linRegCoeffs X μ t0 w j :=
        Equiv.sum_comp σ fun j => cov[X (w (σ l)), X (w j); μ] * linRegCoeffs X μ t0 w j
    _ = cov[X t0, X (w (σ l)); μ] := linRegCoeffs_normalEq t0 w hinv (σ l)
    _ = cov[X (t0 + s), X (w (σ l) + s); μ] := hR.symm

/-- **Leading principal submatrices inherit nonsingularity** for autocovariance Toeplitz
matrices: a kernel vector of `Γ_n` makes the corresponding linear combination of the
process a.s. constant, hence extends by zero to a kernel vector of `Γ_{n+1}`. -/
private lemma isUnit_det_acvfToeplitz_of_succ [IsProbabilityMeasure μ]
    (hstat : IsStationary X μ) {n : ℕ}
    (hinv : IsUnit (acvfToeplitz X μ (n + 1)).det) : IsUnit (acvfToeplitz X μ n).det := by
  classical
  rw [isUnit_iff_ne_zero] at hinv ⊢
  intro h0
  obtain ⟨x, hx, hxz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hrow : ∀ i : Fin n, ∑ j : Fin n, acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j = 0 := by
    intro i
    simpa [Matrix.mulVec, dotProduct, acvfToeplitz] using congrFun hxz i
  have hcovu : ∀ i j : Fin n,
      cov[X (((i : ℕ) : ℤ)), X (((j : ℕ) : ℤ)); μ]
        = acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := fun i j => hstat.cov_eq_acvf _ _
  -- the linear combination has zero variance, hence is a.s. constant
  have hvar : variance (fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω) μ = 0 := by
    rw [variance_fun_sum (fun i : Fin n => (hstat.memLp (((i : ℕ) : ℤ))).const_mul (x i))]
    have hterm : ∀ i j : Fin n,
        cov[fun ω => x i * X (((i : ℕ) : ℤ)) ω, fun ω => x j * X (((j : ℕ) : ℤ)) ω; μ]
          = x i * (acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j) := by
      intro i j
      rw [covariance_const_mul_left, covariance_const_mul_right, hcovu]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show ∑ j : Fin n, acvf X μ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j = 0 from hrow i, mul_zero]
  have hconst : (fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω)
      =ᵐ[μ] fun _ => ∫ ω, ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω ∂μ :=
    ae_eq_integral_of_variance_eq_zero
      (memLp_window hstat (fun i : Fin n => ((i : ℕ) : ℤ)) x) hvar
  have hcovS : ∀ t : ℤ, cov[X t, fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω; μ] = 0 := by
    intro t
    rw [covariance_congr_ae (EventuallyEq.refl _ (X t)) hconst]
    exact covariance_const_right _
  -- extend the kernel vector by zero
  refine hinv (Matrix.exists_mulVec_eq_zero_iff.1
    ⟨fun i : Fin (n + 1) => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0, ?_, ?_⟩)
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact Function.ne_iff.2 ⟨i.castSucc, by simpa using hi⟩
  · funext l
    have hexp : (acvfToeplitz X μ (n + 1) *ᵥ
          fun i : Fin (n + 1) => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0) l
        = ∑ j : Fin n, acvf X μ (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j := by
      simp only [Matrix.mulVec, dotProduct, acvfToeplitz, Matrix.of_apply]
      rw [Fin.sum_univ_castSucc]
      simp
    have hcs : ∑ j : Fin n, acvf X μ (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * x j
        = cov[X (((l : ℕ) : ℤ)), fun ω => ∑ i : Fin n, x i * X (((i : ℕ) : ℤ)) ω; μ] := by
      rw [covariance_fun_sum_right
        (fun j : Fin n => (hstat.memLp (((j : ℕ) : ℤ))).const_mul (x j))
        (hstat.memLp (((l : ℕ) : ℤ)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [covariance_const_mul_right, hstat.cov_eq_acvf]
      ring
    rw [hexp, hcs, hcovS]
    rfl

end Toolkit

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
  -- FY eq. (2.69): `X_{t₀} − βᵀW = R − (β−α)ᵀW`, and the cross term vanishes.
  have hkey : (fun ω => X t0 ω - ∑ i, β i * X (w i) ω)
      = fun ω => linRegResidual X μ t0 w ω
          - ∑ i, (β i - linRegCoeffs X μ t0 w i) * X (w i) ω := by
    funext ω
    simp only [linRegResidual_eq, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hkey, variance_fun_sub (memLp_linRegResidual hstat t0 w)
      (memLp_window hstat w _),
    cov_linRegResidual_windowSum hstat t0 w hinv]
  have := variance_nonneg (fun ω => ∑ i, (β i - linRegCoeffs X μ t0 w i) * X (w i) ω) μ
  linarith

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
