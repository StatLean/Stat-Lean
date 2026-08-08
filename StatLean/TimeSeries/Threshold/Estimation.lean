import StatLean.TimeSeries.Threshold.TAR
import StatLean.TimeSeries.ARMA.Likelihood
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# TAR estimation with a known partition (FY §4.1.2, eqs. (4.4)–(4.8))

Least-squares fitting of a TAR model when the regime partition (and hence the regime
memberships of the observations) is known:

* `tarRegimeIndices` — the time indices falling in regime `i`, and `tarRegimeCount`
  `T_i = #{t : X_{t−d} ∈ A_i}`;
* `tarLSResidualSS` — the regime-`i` residual sum of squares (FY eq. (4.4)) and
  `tarSigmaHatSq` — the regime variance estimate `σ̂_i²` (eq. (4.6));
* `tarGeneralizedAIC` — the order/delay-selection criterion
  `Σ_i [T_i log σ̂_i²(p_i) + 2(p_i + 1)]` (eq. (4.7); the delay `d` is profiled by
  minimizing over the candidate grid, ties broken by the smallest `d` — recorded as
  the definition's tie-break convention);
* **eq. (4.8)** — the known-partition asymptotic normality
  `T_i^{1/2}(b̃_i − b_i) →d N(0, σ_i² W_i^{-1})`, a literature DEBT (the book says
  "can be shown", pointing at Theorem 3.2). **Caution recorded in the inventory and
  honored here**: the printed `W_i` is built from the moments of the *fictitious global
  regime-`i` AR process*, not from moments conditional on `X_{t−d} ∈ A_i`; we state it
  with the fictitious-process reading, matching Chan (1993a).

**Scope.** FY Theorems 4.1/4.2 (Chan 1993a) and their consumers are **descoped**
(user, 2026-08-04); nothing here estimates the threshold `r` itself.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.2,
eqs. (4.4)–(4.8) (pp. 131–134). (`FY §4.1.2`.)

**Bibliographic comments.** Regime-wise least squares for TAR is Tong & Lim (1980);
the known-partition asymptotics are Chan (1993a, Ann. Statist.); the generalized AIC
is Tong (1990) §5.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Time indices (within the usable window `P + 1 ≤ t < T`) whose threshold variable
falls in regime `i` (FY §4.1.2). -/
noncomputable def tarRegimeIndices {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) :
    Finset (Fin T) :=
  Finset.univ.filter fun t : Fin T => P < (t : ℕ) ∧ ∃ h : d ≤ (t : ℕ),
    x ⟨(t : ℕ) - d, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ ∈ A

/-- The regime-`i` sample size `T_i` (FY §4.1.2). -/
noncomputable def tarRegimeCount {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) : ℕ :=
  (tarRegimeIndices x A d P).card

/-- The regime-`i` **residual sum of squares** at coefficients `(β₀, β)`
(FY eq. (4.4)): `Σ_{t ∈ regime i} (x_t − β₀ − Σ_j β_j x_{t−1−j})²`. -/
noncomputable def tarLSResidualSS {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) : ℝ :=
  ∑ t ∈ tarRegimeIndices x A d P,
    (x t - β0 - ∑ j : Fin P, β j *
      x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩) ^ 2

/-- The regime-`i` variance estimate `σ̂_i² = RSS_i / T_i` (FY eq. (4.6); junk `0` when
the regime is empty). -/
noncomputable def tarSigmaHatSq {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) : ℝ :=
  tarLSResidualSS x A d β0 β / (tarRegimeCount x A d P : ℝ)

/-- The **generalized AIC** for TAR order selection (FY eq. (4.7)):
`Σ_i [T_i log σ̂_i²(p_i) + 2(p_i + 1)]`, evaluated at given regime fits. -/
noncomputable def tarGeneralizedAIC {k T P : ℕ} (x : Fin T → ℝ) (A : Fin k → Set ℝ)
    (d : ℕ) (β0 : Fin k → ℝ) (β : Fin k → Fin P → ℝ) (porder : Fin k → ℕ) : ℝ :=
  ∑ i, ((tarRegimeCount x (A i) d P : ℝ) *
      Real.log (tarSigmaHatSq x (A i) d (β0 i) (β i))
    + 2 * ((porder i : ℝ) + 1))

/-- The regime-`i` least-squares fit is characterized by its normal equations
(the finite-dimensional projection; no invertibility needed for existence). -/
theorem exists_tarLS_minimizer {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ) :
    ∃ (β0 : ℝ) (β : Fin P → ℝ), ∀ (γ0 : ℝ) (γ : Fin P → ℝ),
      tarLSResidualSS x A d β0 β ≤ tarLSResidualSS x A d γ0 γ := by
  sorry

/-- **FY eq. (4.8) — DEBT (Chan 1993a; the book's "can be shown", companion to
Thm 3.2)**: with a known partition, under strict stationarity, ergodicity and finite
second moments, the regime-wise LS estimator is `√T_i`-asymptotically normal with
covariance `σ_i² W_i^{-1}`, where `W_i` is the second-moment matrix of the
**fictitious global regime-`i` AR process** (the inventory's documented reading of the
printed `W_i`, per Chan 1993a — *not* the conditional moments given `X_{t−d} ∈ A_i`).
Stated in Cramér–Wold/charFun form over the coefficient vector. -/
theorem tarLS_clt_debt [IsProbabilityMeasure μ] {k P : ℕ}
    {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ : Fin k → ℝ} {A : Fin k → Set ℝ}
    {d : ℕ} {X ε : ℤ → Ω → ℝ}
    (h : IsTAR b0 b σ A d X ε μ)
    -- USER-INPUT: strict stationarity of the fitted process; FY §4.1.2 standing assumption
    (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: finite second moments; FY §4.1.2 standing assumption
    (hL2 : ∀ t, MemLp (X t) 2 μ)
    -- USER-INPUT: the fictitious regime-i AR process' second-moment matrix, assumed
    -- invertible; Chan 1993a
    (i : Fin k) (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef)
    -- USER-INPUT: a measurable regime-wise LS estimator sequence; FY eqs. (4.4)-(4.5)
    (bhat : (T : ℕ) → Ω → Fin P → ℝ) (hmeas : ∀ T, Measurable (bhat T))
    (hLS : ∀ (T : ℕ) (ω : Ω), ∀ γ0 : ℝ, ∀ γ : Fin P → ℝ,
      tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d
          (b0 i) (bhat T ω)
        ≤ tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d γ0 γ)
    (c : Fin P → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt (tarRegimeCount (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d P) *
          ∑ j, c j * (bhat T ω j - b i j)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σ i ^ 2 * (c ⬝ᵥ (W⁻¹ *ᵥ c))))) u)) := by
  sorry

end StatLean.TimeSeries
