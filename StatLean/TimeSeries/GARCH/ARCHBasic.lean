import StatLean.TimeSeries.Stationarity.ARCH
import StatLean.TimeSeries.Stationarity.ARMAExistence
import StatLean.TimeSeries.Models.Linear
import StatLean.TimeSeries.Process.LinearProcess

/-!
# Basic properties of ARCH(p) (FY §4.2.1, Theorem 4.3, Proposition 4.1)

The finite-order ARCH theory, all of it routed through the ARCH(∞) Volterra machinery
of `Stationarity/ARCH.lean` (FY Theorem 2.5) — §2.1.4's Markov apparatus is never used
in §4.2:

* **Theorem 4.3(i)** (sufficiency half): `Σ_j b_j < 1` ⇒ a unique strictly stationary
  ARCH(p) solution with `E X_t² < ∞`, and then `E X_t = 0`,
  `E X_t² = c₀/(1 − Σ b_j)`; `c₀ = 0` forces `X ≡ 0`. Proof: apply Theorem 2.5 with
  `Y_t = X_t²`, `ξ_t = ε_t²`, then read off the moments by stationarity. The
  **necessity** half is Bollerslev (1986) Thm 1 — a literature DEBT.
* **Theorem 4.3(ii)**: `E ε⁴ < ∞` and eq. (4.16) `max{1, (Eε⁴)^{1/2}} Σ b_j < 1`
  ⇒ `E X_t⁴ < ∞`.
* **eqs. (4.17)–(4.20)**: `X_t²` satisfies an AR(p) recursion whose noise
  `e_t = (ε_t² − 1)σ_t²` is a **martingale difference** (eq. (4.18)); under (4.16) it
  is white noise, and since `Σ b_j < 1` forces `1 − Σ b_j z^j ≠ 0` on `|z| ≤ 1`, the
  squared process is a **causal AR(p)** — so its ACF is the ARMA machinery's, and it
  is strictly positive at every lag when `Σ b_j > 0`.
* **eq. (4.21)**: kurtosis dominance `κ_x ≥ κ_ε` (tower + Jensen).
* **Proposition 4.1**: the packaging of the three previous items.
* **Example 4.1 (ARCH(1))**, eqs. (4.22)–(4.23): the geometric `k`-step conditional
  variance, `Corr(X_t², X_{t+τ}²) = b₁^{|τ|}`, and — for normal errors —
  `(4.16) ⇔ 3b₁² < 1` with `κ_x = 3(1 − b₁²)/(1 − 3b₁²)`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.1,
Definition 4.2, Theorem 4.3, Proposition 4.1, eqs. (4.15)–(4.23) (pp. 143–147).
(`FY §4.2.1`.)

**Bibliographic comments.** ARCH is R. F. Engle, *Autoregressive conditional
heteroscedasticity with estimates of the variance of United Kingdom inflation*
(Econometrica 50 (1982), 987–1007); the stationarity characterization is Bollerslev
(1986) Thm 1; the Volterra route used here is Giraitis, Kokoszka & Leipus (2000).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The ARCH(p) coefficient sequence read as an ARCH(∞) sequence (zero-padded), so the
§2.1.5 theory applies verbatim to `Y_t = X_t²`, `ξ_t = ε_t²`. -/
noncomputable def archInfCoeffs {p : ℕ} (b : Fin p → ℝ) : ℕ → ℝ := fun j =>
  if h : j < p then b ⟨j, h⟩ else 0

/-- The squared ARCH(p) process is an ARCH(∞) process in the sense of `IsARCHInf`
(FY §4.2.1's reduction to Theorem 2.5). -/
theorem IsARCH.isARCHInf_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ) :
    IsARCHInf c0 (archInfCoeffs b) (fun t ω => X t ω ^ 2) (fun t ω => ε t ω ^ 2) μ := by
  sorry

/-- **FY Theorem 4.3(i), existence + moments**: under `Σ_j b_j < 1` there is a strictly
stationary ARCH(p) solution with finite variance, and every such solution has
`E X_t = 0` and `E X_t² = c₀/(1 − Σ b_j)`. -/
theorem exists_stationary_arch [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: nonnegative coefficients; FY Def 4.2
    (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i)
    -- USER-INPUT: contraction; FY Thm 4.3(i)
    (hsum : (∑ i, b i) < 1)
    -- USER-INPUT: iid(0,1) innovations; FY Def 4.2
    (hε : IsIIDNoise ε 1 μ) :
    ∃ X : ℤ → Ω → ℝ, IsARCH c0 b X ε μ ∧ IsStrictlyStationary X μ ∧
      (∀ t, MemLp (X t) 2 μ) := by
  sorry

/-- **FY Theorem 4.3(i), moment identities**: a stationary square-integrable ARCH(p)
process is centered with variance `c₀/(1 − Σ b_j)`. -/
theorem IsARCH.integral_and_variance [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) < 1) (t : ℤ) :
    (∫ ω, X t ω ∂μ) = 0 ∧ variance (X t) μ = c0 / (1 - ∑ i, b i) := by
  sorry

/-- **FY Theorem 4.3(i), degenerate case**: `c₀ = 0` forces the stationary solution to
vanish. -/
theorem IsARCH.eq_zero_of_c0_eq_zero [IsProbabilityMeasure μ] {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH 0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) < 1) (t : ℤ) :
    X t =ᵐ[μ] 0 := by
  sorry

/-- **DEBT (Bollerslev 1986 Thm 1; FY Theorem 4.3(i), necessity half)**: conversely, a
strictly stationary ARCH(p) solution with finite variance forces `Σ_j b_j < 1`. -/
theorem IsARCH.sum_lt_one_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    -- USER-INPUT: nondegeneracy (c₀ > 0 rules out the trivial solution); FY Thm 4.3(i)
    (hc0 : 0 < c0) :
    (∑ i, b i) < 1 := by
  sorry

/-- **FY Theorem 4.3(ii)** (eq. (4.16)): a finite fourth innovation moment together with
`max{1, (Eε⁴)^{1/2}}·Σ b_j < 1` gives a finite fourth moment for the process. -/
theorem IsARCH.memLp_four [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: finite fourth innovation moment; FY Thm 4.3(ii)
    (hε4 : MemLp (ε 0) 4 μ)
    -- USER-INPUT: eq. (4.16); FY Thm 4.3(ii)
    (h416 : max 1 (Real.sqrt (∫ ω, ε 0 ω ^ 4 ∂μ)) * (∑ i, b i) < 1)
    (t : ℤ) :
    MemLp (X t) 4 μ := by
  sorry

/-- **FY eq. (4.18)**: the squared-process innovations `e_t = (ε_t² − 1)σ_t²` are a
martingale difference with respect to the strict past of `X`. -/
theorem IsARCH.condexp_sq_innovation [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[fun ω => (ε t ω ^ 2 - 1) * archVol c0 b X t ω ^ 2 | sigmaLT X t] =ᵐ[μ] 0 := by
  sorry

/-- **FY eq. (4.17)**: the squared process satisfies the AR(p) recursion
`X_t² = c₀ + Σᵢ bᵢ X_{t−i}² + e_t` with `e_t = (ε_t² − 1)σ_t²`. -/
theorem IsARCH.sq_ar_recursion [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ) (t : ℤ) :
    (fun ω => X t ω ^ 2) =ᵐ[μ] fun ω =>
      c0 + (∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2)
        + (ε t ω ^ 2 - 1) * archVol c0 b X t ω ^ 2 := by
  sorry

/-- **FY §4.2.1**: `Σ b_j < 1` with nonnegative coefficients forces the AR polynomial of
the squared process to be root-free on the closed unit disc — hence `{X_t²}` is a
*causal* AR(p) (FY eq. (4.20)). -/
theorem noRootClosedDisc_of_sum_lt_one {p : ℕ} {b : Fin p → ℝ}
    (hb : ∀ i, 0 ≤ b i) (hsum : (∑ i, b i) < 1) :
    NoRootClosedDisc b := by
  sorry

/-- **FY eq. (4.21) / Proposition 4.1(iii)**: an ARCH process is at least as leptokurtic
as its innovations, `κ_x ≥ κ_ε` (equivalently `E X⁴ · (E ε²)² ≥ E ε⁴ · (E X²)²`; stated
in the product form to avoid division). -/
theorem IsARCH.kurtosis_le [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    (hε4 : MemLp (ε 0) 4 μ) :
    (∫ ω, ε 0 ω ^ 4 ∂μ) * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2
      ≤ (∫ ω, X 0 ω ^ 4 ∂μ) * (∫ ω, ε 0 ω ^ 2 ∂μ) ^ 2 := by
  sorry

/-- **FY Proposition 4.1(i)**: a stationary ARCH(p) process is white noise with variance
`c₀/(1 − Σ b_j)`. -/
theorem IsARCH.isWhiteNoise [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) < 1) :
    IsWhiteNoise X (c0 / (1 - ∑ i, b i)) μ := by
  sorry

/-- **FY Example 4.1, eq. (4.23)**: for a stationary ARCH(1) with finite fourth moment,
the squared process has autocorrelation `Corr(X_t², X_{t+τ}²) = b₁^{|τ|}`. -/
theorem IsARCH.acf_sq_arch_one [IsProbabilityMeasure μ] {c0 b1 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 (fun _ : Fin 1 => b1) X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    (hb1 : 0 < b1) (hb1' : b1 < 1)
    -- USER-INPUT: nondegenerate squared process; FY Example 4.1
    (hvar : 0 < variance (fun ω => X 0 ω ^ 2) μ) (τ : ℤ) :
    acf (fun t ω => X t ω ^ 2) μ τ = b1 ^ τ.natAbs := by
  sorry

/-- **FY Example 4.1**, normal-error specialization: for `ε ∼ N(0,1)`, condition (4.16)
reads `3b₁² < 1`, and then the kurtosis is `κ_x = 3(1 − b₁²)/(1 − 3b₁²)`. -/
theorem IsARCH.kurtosis_arch_one_gaussian [IsProbabilityMeasure μ] {c0 b1 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 (fun _ : Fin 1 => b1) X ε μ)
    (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: standard normal innovations; FY Example 4.1
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hb1 : 0 < b1) (h3b : 3 * b1 ^ 2 < 1) (hc0 : 0 < c0) :
    MemLp (X 0) 4 μ ∧
      (∫ ω, X 0 ω ^ 4 ∂μ) * (1 - 3 * b1 ^ 2)
        = 3 * (1 - b1 ^ 2) * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2 := by
  sorry

end StatLean.TimeSeries
