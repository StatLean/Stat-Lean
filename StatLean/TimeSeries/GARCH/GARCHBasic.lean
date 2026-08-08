import StatLean.TimeSeries.GARCH.ARCHBasic

/-!
# Basic properties of GARCH(p, q) (FY §4.2.2, Theorem 4.4, Proposition 4.2)

* **ARCH(∞) reduction** (FY p. 148): inverting `1 − Σ_j a_j B^j` turns the GARCH
  volatility recursion into an ARCH(∞) one with nonnegative coefficients `d_i`
  (recursion as in eq. (2.20)) — this is how Theorem 2.5 applies.
* **Theorem 4.4** (sufficiency half): `Σ b_i + Σ a_j < 1` ⇒ a unique strictly
  stationary solution with `E X_t² < ∞`; then `E X_t = 0`,
  `Var X_t = c₀/(1 − Σb − Σa)`, and `X` is white noise. Finite fourth moments hold
  under eq. (4.28). The **necessity** half is Bollerslev (1986) — literature DEBT.
* **eqs. (4.25)–(4.26)**: `X_t²` follows an ARMA(p∨q, q) with martingale-difference
  noise `e_t = (ε_t² − 1)σ_t²`.
* **Proposition 4.2**: stationary GARCH is white noise, `σ_t²` is the conditional
  variance given the **infinite** past, and (under (4.28)) `{X_t²}` is a causal
  invertible ARMA with `κ_x ≥ κ_ε`.
* **Example 4.2**, eqs. (4.29)–(4.30): the GARCH(1,1) ARCH(∞) form and the closed-form
  squared-process ACF
  `Corr(X_t², X_{t+k}²) = ((1 − a₁² − a₁b₁)b₁ / (1 − a₁² − 2a₁b₁))·(b₁ + a₁)^{k−1}`.
* **Nelson (1990) sufficiency — a COMMISSIONED PROOF TARGET** (user, 2026-08-04):
  `E log(b₁ε² + a₁) < 0` ⇒ GARCH(1,1) has a unique strictly stationary solution, via
  the a.s. convergence of the random-product series `Σ_k ∏_{i<k}(b₁ε²_{t−i} + a₁)`
  (iid SLLN on the logs), *without* any moment condition; and the **IGARCH(1,1)**
  corollary: `b₁ + a₁ = 1` with nondegenerate `ε²` still gives strict stationarity,
  because strict Jensen makes `E log(b₁ε² + a₁) < log E(b₁ε² + a₁) = 0`.

**Scope.** Descoped 2026-08-04 (user), with all consumers: Nelson **necessity**,
Bougerol–Picard (1992b) Lyapunov-exponent iff and the general-`(p,q)` IGARCH
eq. (4.33), Kesten (1973) tail index eqs. (4.31)–(4.32). None is stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.2,
Definition 4.3, Theorem 4.4, Proposition 4.2, eqs. (4.24)–(4.30) (pp. 147–156).
(`FY §4.2.2`.)

**Bibliographic comments.** GARCH is T. Bollerslev, *Generalized autoregressive
conditional heteroskedasticity* (J. Econometrics 31 (1986), 307–327); the strict
stationarity criterion for GARCH(1,1) is D. B. Nelson, *Stationarity and persistence in
the GARCH(1,1) model* (Econometric Theory 6 (1990), 318–334).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **ARCH(∞) coefficients of a GARCH(p, q)** (FY p. 148): the coefficients `d_i` of
`(Σ_i b_i z^i)/(1 − Σ_j a_j z^j)`, obtained as formal power-series coefficients. -/
noncomputable def garchInfCoeffs {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (i : ℕ) :
    ℝ :=
  PowerSeries.coeff i
    (((∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) :
        Polynomial ℝ) : PowerSeries ℝ) *
      (((arPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

/-- The GARCH ARCH(∞) coefficients are nonnegative under nonnegative GARCH
coefficients (FY p. 148: "the recursion has nonnegative solutions like (2.20)"). -/
theorem garchInfCoeffs_nonneg {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) < 1) (i : ℕ) :
    0 ≤ garchInfCoeffs b a i := by
  sorry

/-- Their total mass: `Σ_i d_i = (Σ b_i)/(1 − Σ a_j)`, which is `< 1` exactly when
`Σ b + Σ a < 1` — the bridge from FY Theorem 4.4's hypothesis to Theorem 2.5's. -/
theorem tsum_garchInfCoeffs {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) < 1) :
    HasSum (garchInfCoeffs b a) ((∑ i, b i) / (1 - ∑ j, a j)) := by
  sorry

/-- **FY Theorem 4.4, existence**: under `Σ b + Σ a < 1` a strictly stationary
square-integrable GARCH(p, q) solution exists. -/
theorem exists_stationary_garch [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: nonnegative coefficients; FY Def 4.3
    (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j)
    -- USER-INPUT: contraction; FY Thm 4.4
    (hsum : (∑ i, b i) + (∑ j, a j) < 1)
    -- USER-INPUT: iid(0,1) innovations; FY Def 4.3
    (hε : IsIIDNoise ε 1 μ) :
    ∃ X σvol : ℤ → Ω → ℝ, IsGARCH c0 b a X σvol ε μ ∧ IsStrictlyStationary X μ ∧
      (∀ t, MemLp (X t) 2 μ) := by
  sorry

/-- **FY Theorem 4.4, moments**: a stationary square-integrable GARCH process is
centered with variance `c₀/(1 − Σb − Σa)`. -/
theorem IsGARCH.integral_and_variance [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) + (∑ j, a j) < 1) (t : ℤ) :
    (∫ ω, X t ω ∂μ) = 0 ∧
      variance (X t) μ = c0 / (1 - (∑ i, b i) - ∑ j, a j) := by
  sorry

/-- **FY Proposition 4.2(i)**: a stationary GARCH process is white noise. -/
theorem IsGARCH.isWhiteNoise [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (hsum : (∑ i, b i) + (∑ j, a j) < 1) :
    IsWhiteNoise X (c0 / (1 - (∑ i, b i) - ∑ j, a j)) μ := by
  sorry

/-- **FY Proposition 4.2(i)**: `σ_t²` is the conditional variance of `X_t` given the
strict past. -/
theorem IsGARCH.condexp_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[fun ω => X t ω ^ 2 | sigmaLT X t] =ᵐ[μ] fun ω => σvol t ω ^ 2 := by
  sorry

/-- **FY eqs. (4.25)–(4.26)**: the squared process satisfies the ARMA(p∨q, q) recursion
`X_t² = c₀ + Σ_{i ≤ p∨q}(b_i + a_i) X_{t−i}² + e_t − Σ_j a_j e_{t−j}` with the
martingale-difference noise `e_t = (ε_t² − 1)σ_t²` (coefficients zero-padded to the
common order). -/
theorem IsGARCH.sq_arma_recursion [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (t : ℤ) :
    (fun ω => X t ω ^ 2) =ᵐ[μ] fun ω =>
      c0 + (∑ i ∈ Finset.range (max p q),
          ((if hi : i < p then b ⟨i, hi⟩ else 0) + (if hi : i < q then a ⟨i, hi⟩ else 0))
            * X (t - 1 - (i : ℕ)) ω ^ 2)
        + ((ε t ω ^ 2 - 1) * σvol t ω ^ 2)
        - ∑ j : Fin q, a j * ((ε (t - 1 - (j : ℕ)) ω ^ 2 - 1)
            * σvol (t - 1 - (j : ℕ)) ω ^ 2) := by
  sorry

/-- **DEBT (Bollerslev 1986; FY Theorem 4.4, necessity half)**: a strictly stationary
GARCH solution with finite variance and `c₀ > 0` forces `Σ b + Σ a < 1`. -/
theorem IsGARCH.sum_lt_one_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (hc0 : 0 < c0) :
    (∑ i, b i) + (∑ j, a j) < 1 := by
  sorry

/-- **FY Example 4.2, eq. (4.30)**: the squared-process ACF of a stationary GARCH(1,1)
with finite fourth moment is
`Corr(X_t², X_{t+k}²) = ((1 − a₁² − a₁b₁)b₁/(1 − a₁² − 2a₁b₁))·(b₁ + a₁)^{k−1}`
for `k ≥ 1`. -/
theorem IsGARCH.acf_sq_garch_one_one [IsProbabilityMeasure μ] {c0 b1 a1 : ℝ}
    {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    (hb1 : 0 < b1) (ha1 : 0 ≤ a1) (hsum : b1 + a1 < 1)
    -- USER-INPUT: nondegenerate denominator; FY eq. (4.30)
    (hden : 1 - a1 ^ 2 - 2 * a1 * b1 ≠ 0)
    (hvar : 0 < variance (fun ω => X 0 ω ^ 2) μ) {k : ℕ} (hk : 1 ≤ k) :
    acf (fun t ω => X t ω ^ 2) μ (k : ℤ)
      = ((1 - a1 ^ 2 - a1 * b1) * b1 / (1 - a1 ^ 2 - 2 * a1 * b1))
        * (b1 + a1) ^ (k - 1) := by
  sorry

/-! ### Nelson's strict-stationarity criterion (commissioned proof target) -/

/-- **Nelson (1990), sufficiency — COMMISSIONED PROOF TARGET** (user, 2026-08-04):
if `E log(b₁ ε₀² + a₁) < 0` then the GARCH(1,1) equations admit a strictly stationary
solution, *with no moment condition on `ε`*. The volatility is the a.s.-convergent
random-product series `σ_t² = c₀ Σ_{k ≥ 0} ∏_{i < k} (b₁ ε_{t−1−i}² + a₁)`, whose
convergence comes from the iid strong law applied to the logs. -/
theorem exists_strictlyStationary_garch_one_one_nelson [IsProbabilityMeasure μ]
    {c0 b1 a1 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: nonnegative coefficients; FY Def 4.3
    (hc0 : 0 < c0) (hb1 : 0 < b1) (ha1 : 0 ≤ a1)
    -- USER-INPUT: iid(0,1) innovations; FY Def 4.3
    (hε : IsIIDNoise ε 1 μ)
    -- LEAN-ONLY: integrability of the log-multiplier (implicit in Nelson's E log < 0)
    (hlogint : Integrable (fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1)) μ)
    -- USER-INPUT: Nelson's condition; Nelson 1990 Thm 2
    (hnelson : (∫ ω, Real.log (b1 * ε 0 ω ^ 2 + a1) ∂μ) < 0) :
    ∃ X σvol : ℤ → Ω → ℝ,
      IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ ∧
        IsStrictlyStationary X μ := by
  sorry

/-- **IGARCH(1,1)** (the `(p,q) = (1,1)` case of FY eq. (4.33), the only case in scope):
when `b₁ + a₁ = 1` and `ε²` is nondegenerate, strict Jensen gives
`E log(b₁ε² + a₁) < log E(b₁ε² + a₁) = log 1 = 0`, so Nelson's criterion applies and a
strictly stationary IGARCH(1,1) solution exists — even though no stationary solution
with finite variance does (FY Theorem 4.4). -/
theorem exists_strictlyStationary_igarch_one_one [IsProbabilityMeasure μ]
    {c0 b1 a1 : ℝ} {ε : ℤ → Ω → ℝ}
    (hc0 : 0 < c0) (hb1 : 0 < b1) (ha1 : 0 ≤ a1)
    -- USER-INPUT: the integrated-GARCH boundary; FY eq. (4.33) at (p,q) = (1,1)
    (hunit : b1 + a1 = 1)
    (hε : IsIIDNoise ε 1 μ)
    (hlogint : Integrable (fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1)) μ)
    -- USER-INPUT: nondegenerate innovations (needed for STRICT Jensen); Nelson 1990
    (hnondeg : ¬ (fun ω => ε 0 ω ^ 2) =ᵐ[μ] fun _ => (1 : ℝ)) :
    ∃ X σvol : ℤ → Ω → ℝ,
      IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ ∧
        IsStrictlyStationary X μ := by
  sorry

end StatLean.TimeSeries
