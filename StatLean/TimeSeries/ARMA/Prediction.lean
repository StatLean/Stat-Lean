import StatLean.TimeSeries.Process.PartialAutocorrelation

/-!
# Best linear prediction and prewhitening (FY §3.2, Definition 3.1, Theorem 3.1)

For a zero-mean weakly stationary process:

* the **mean-squared prediction error** of a linear predictor of `X_{k+1}` from
  `X_k, …, X_1` (`predMSE`; FY eqs. (3.3)–(3.4));
* **FY Theorem 3.1**: a coefficient vector is MSE-optimal **iff** it solves the
  Yule–Walker system `Σ_j φ_{kj} γ(i − j) = γ(i)`, `i = 1..k` (eq. (3.5)) — full
  in-text proof (quadratic expansion (3.6) + perturbation necessity);
* **prewhitening**: successive innovations `X_{t+1} − X̂_{t+1}` are uncorrelated
  (corollary of the projection orthogonality);
* the **innovation variances** `ν_t = γ(0) − Σ_j φ_{tj} γ(j)` (eq. (3.7));
* the **innovation algorithm** (B&D Prop 5.2.2) — Gram–Schmidt recursion for the
  one-step predictors; stated as a correctness claim for the recursively defined
  coefficients, proof attempted (demoted to a named debt if it exceeds the wave
  budget, per the roadmap).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.2,
Definition 3.1, Theorem 3.1, eqs. (3.3)–(3.8) (pp. 91–93). (`FY §3.2`.)

**Proof formalization notes.**
* The predictor window is `X_1, …, X_k` predicting `X_{k+1}`, per FY's indexing; the
  time reversal against `Process/PartialAutocorrelation.lean`'s
  `linRegCoeffs`-machinery is handled by `acvf_even`.
* `predMSE` is an integral of a square, not a `variance` — the process is zero-mean by
  hypothesis, keeping the statements free of centering.

**Bibliographic comments.** Best linear prediction of stationary sequences is
Kolmogorov (1941) and Wiener (1949); the finite-window normal-equation form is
standard from Brockwell & Davis (1991) §5.1; the innovation algorithm is B&D
Prop 5.2.2 (after Rissanen–Barbosa).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Mean-squared prediction error** (FY eq. (3.4)) of predicting `X_{k+1}` by
`Σ_{j<k} φ_j X_{k−j}` (so `φ_0` weights the most recent observation `X_k`). -/
noncomputable def predMSE (X : ℤ → Ω → ℝ) (μ : Measure Ω) (k : ℕ)
    (φ : Fin k → ℝ) : ℝ :=
  ∫ ω, (X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω) ^ 2 ∂μ

/-- **FY Theorem 3.1**: for a zero-mean weakly stationary process, `φ` minimizes the
prediction MSE **iff** it solves the Yule–Walker system (3.5)
`Σ_j φ_j γ(i − j) = γ(i)` for `i = 1..k` (lag bookkeeping: predicting one step ahead
from the `k` most recent values). -/
theorem predMSE_isMinOn_iff_yuleWalker [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    -- USER-INPUT: zero mean; FY §3.2 standing assumption
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {k : ℕ} (φ : Fin k → ℝ) :
    (∀ ψ : Fin k → ℝ, predMSE X μ k φ ≤ predMSE X μ k ψ) ↔
      ∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
        = acvf X μ ((i : ℕ) + 1) := by
  sorry

/-- **Prewhitening** (FY §3.2, consequence of Thm 3.1's orthogonality): innovations at
different horizons are uncorrelated: if `φ` and `ψ` are Yule–Walker solutions at
horizons `k < l`, the corresponding innovations have zero covariance. -/
theorem innovations_uncorrelated [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {k l : ℕ} (hkl : k < l) {φ : Fin k → ℝ} {ψ : Fin l → ℝ}
    -- USER-INPUT: both are Yule–Walker solutions; FY Thm 3.1
    (hφ : ∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
      = acvf X μ ((i : ℕ) + 1))
    (hψ : ∀ i : Fin l, ∑ j, ψ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
      = acvf X μ ((i : ℕ) + 1)) :
    cov[fun ω => X ((k : ℤ) + 1) ω - ∑ j, φ j * X ((k : ℤ) - (j : ℕ)) ω,
        fun ω => X ((l : ℤ) + 1) ω - ∑ j, ψ j * X ((l : ℤ) - (j : ℕ)) ω; μ] = 0 := by
  sorry

/-- **Innovation variance identity** (FY eq. (3.7)): at a Yule–Walker solution,
`predMSE = ν_k = γ(0) − Σ_j φ_j γ(j+1)`. -/
theorem predMSE_eq_innovation_variance [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {k : ℕ} {φ : Fin k → ℝ}
    (hφ : ∀ i : Fin k, ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ)
      = acvf X μ ((i : ℕ) + 1)) :
    predMSE X μ k φ = acvf X μ 0 - ∑ j, φ j * acvf X μ ((j : ℕ) + 1) := by
  sorry

/-- Existence of a Yule–Walker solution at every horizon (the finite-dimensional
projection always exists; no invertibility needed — FY takes it silently from the
projection formulation of Definition 3.1). -/
theorem exists_yuleWalker_solution [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStationary X μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (k : ℕ) :
    ∃ φ : Fin k → ℝ, ∀ i : Fin k,
      ∑ j, φ j * acvf X μ ((i : ℕ) - (j : ℕ) : ℤ) = acvf X μ ((i : ℕ) + 1) := by
  sorry

end StatLean.TimeSeries
