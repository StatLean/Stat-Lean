import StatLean.TimeSeries.GARCH.GARCHBasic
import StatLean.TimeSeries.Spectral.Periodogram
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# GARCH estimation: QMLE, general-density MLE, Whittle, LAD (FY §4.2.3)

Definitions only, plus the two cited asymptotic statements as literature debts:

* **eq. (4.35)/(4.36)**: the ARCH(∞) expansion of the GARCH volatility and its
  **truncated** version `σ̃_t²(θ)` (started from a fixed presample constant), the object
  every practical criterion uses *(the printed `𝐛 = (b₁ … b_p)²` in (4.36) is a typo for
  the coefficient vector — we take the intended reading)*;
* **eq. (4.37)**: the Gaussian quasi-likelihood criterion
  `l_ν(θ) = Σ_{t=ν}^{T}(log σ̃_t² + X_t²/σ̃_t²)`, minimized to give the QMLE;
* **eq. (4.38)**: the general-density criterion `Σ_t (log σ̃_t − log f(X_t/σ̃_t))`, with
  the standardized-`t` and generalized-Gaussian densities recorded as instances;
* **eqs. (4.39)–(4.40)**: AIC/BIC for GARCH order selection;
* **eq. (4.41)**: the Whittle criterion on the squared process, built from the
  periodogram of `Y_t = X_t²` against the model spectral density — its asymptotics are
  a DEBT (Giraitis & Robinson 2001);
* **eq. (4.42)**: the LAD criterion in the median-1 reparametrization — `√T`-normality
  is a DEBT (Peng & Yao 2002).

**Scope.** §4.2.4 (Hall–Yao Theorems 4.5/4.6) and §4.2.5 (bootstrap CIs) were
**descoped on 2026-08-04** at the user's direction, together with the stable-law /
domain-of-attraction scaffolding that existed only to state them. The QMLE definitions
stay because §4.2.6's tests consume them.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.3,
eqs. (4.35)–(4.42) (pp. 156–161). (`FY §4.2.3`.)

**Bibliographic comments.** Gaussian QMLE for GARCH is Bollerslev & Wooldridge (1992);
the Whittle estimator for squared GARCH is Giraitis & Robinson, *Whittle estimation of
ARCH models* (Econometric Theory 17 (2001), 608–631); the LAD estimator is Peng & Yao,
*Least absolute deviations estimation for ARCH and GARCH models* (Biometrika 90 (2003),
967–975).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology Real

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY eq. (4.36)**: the **truncated conditional variance** of a GARCH(p, q) at
parameter `(c₀, b, a)`, computed from the data by running the volatility recursion
forward from a presample constant `v₀ ≥ 0` (the recursion is over the ARCH(∞) form, so
only past data enter). -/
noncomputable def garchTruncVol {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) : ℕ → ℝ
  | 0 => v0
  | (n + 1) =>
      c0 + (∑ i : Fin p, b i * (if h : n - (i : ℕ) < T then x ⟨n - (i : ℕ), h⟩ else 0) ^ 2)
        + ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (n - (j : ℕ))
  decreasing_by all_goals omega

/-- **FY eq. (4.37)**: the Gaussian **quasi-likelihood criterion**
`l_ν(θ) = Σ_{t=ν}^{T−1} (log σ̃_t² + X_t²/σ̃_t²)`; the QMLE minimizes it over the
admissible parameter set. -/
noncomputable def garchQuasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    (Real.log (garchTruncVol c0 b a v0 x t)
      + (if h : t < T then x ⟨t, h⟩ else 0) ^ 2 / garchTruncVol c0 b a v0 x t)

/-- **FY eq. (4.38)**: the **general-density criterion**
`Σ_t (log σ̃_t − log f(X_t/σ̃_t))` for a known standardized innovation density `f`. -/
noncomputable def garchDensityLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) (f : ℝ → ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    (Real.log (Real.sqrt (garchTruncVol c0 b a v0 x t))
      - Real.log (f ((if h : t < T then x ⟨t, h⟩ else 0)
          / Real.sqrt (garchTruncVol c0 b a v0 x t))))

/-- **FY eq. (4.39)**: AIC for GARCH order selection (`2(p + q + 1)` parameters). -/
noncomputable def garchAIC {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  garchQuasiLik c0 b a v0 x ν + 2 * ((p : ℝ) + (q : ℝ) + 1)

/-- **FY eq. (4.40)**: BIC for GARCH order selection. -/
noncomputable def garchBIC {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  garchQuasiLik c0 b a v0 x ν + ((p : ℝ) + (q : ℝ) + 1) * Real.log T

/-- **FY eq. (4.41)**: the **Whittle criterion** for the squared process — the
periodogram of `Y_t = X_t²` integrated against the reciprocal model spectral density,
in the discrete Fourier-frequency form. `gmodel` is the model spectral density of the
squared process at the candidate parameter. -/
noncomputable def garchWhittle {T : ℕ} (x : Fin T → ℝ) (gmodel : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 T,
    (Real.log (gmodel (fourierFreq T k))
      + periodogram (fun t => x t ^ 2) k / gmodel (fourierFreq T k))

/-- **FY eq. (4.42)**: the **LAD criterion** in the median-1 reparametrization:
`Σ_t |log X_t² − log σ̃_t²|`, minimized over the admissible set. -/
noncomputable def garchLAD {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    |Real.log ((if h : t < T then x ⟨t, h⟩ else 0) ^ 2)
      - Real.log (garchTruncVol c0 b a v0 x t)|

/-- The truncated conditional variance is nonnegative under nonnegative parameters and
presample value — the sanity fact every criterion needs for its logarithms. -/
theorem garchTruncVol_nonneg {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {v0 : ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hv0 : 0 ≤ v0)
    {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    0 ≤ garchTruncVol c0 b a v0 x n := by
  sorry

/-- **The truncation is asymptotically negligible** (the fact that makes (4.36) usable):
under `Σ a_j < 1` the effect of the presample value decays geometrically, so two
presample choices give criteria differing by `O(ρ^ν)`. -/
theorem garchTruncVol_presample_stable {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j)
    (hsum : (∑ j, a j) < 1) {v0 v1 : ℝ} (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1)
    {T : ℕ} (x : Fin T → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |garchTruncVol c0 b a v0 x n - garchTruncVol c0 b a v1 x n|
        ≤ C * (∑ j, a j) ^ n := by
  sorry

/-- **DEBT (Giraitis & Robinson 2001; FY §4.2.3)**: `√T`-asymptotic normality of the
Whittle estimator of a GARCH model under fourth-order stationarity. Recorded at the
granularity FY cites (Cramér–Wold/charFun form against an assumed limiting covariance
matrix). -/
theorem whittle_clt_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: fourth-order stationarity; FY §4.2.3 / GR 2001
    (hL4 : ∀ t, MemLp (X t) 4 μ)
    -- USER-INPUT: the limiting covariance matrix of the Whittle estimator; GR 2001
    (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ) (hW : W.PosDef)
    -- USER-INPUT: a measurable Whittle-minimizing estimator sequence; FY eq. (4.41)
    (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ) (hmeas : ∀ T, Measurable (θhat T))
    (θ0 : Fin (p + q + 1) → ℝ)
    (c : Fin (p + q + 1) → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i * c j * W i j))) u)) := by
  sorry

/-- **DEBT (Peng & Yao 2002/2003; FY §4.2.3)**: `√T`-asymptotic normality of the LAD
estimator, which unlike the QMLE needs no moment condition beyond the model's own —
the heavy-tail-robust alternative FY highlights. -/
theorem lad_clt_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: median-1 normalization of the squared innovations; Peng & Yao
    (hmed : μ {ω | ε 0 ω ^ 2 ≤ 1} = μ {ω | 1 ≤ ε 0 ω ^ 2})
    (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ) (hW : W.PosDef)
    (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ) (hmeas : ∀ T, Measurable (θhat T))
    (θ0 : Fin (p + q + 1) → ℝ)
    (c : Fin (p + q + 1) → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i * c j * W i j))) u)) := by
  sorry

end StatLean.TimeSeries
