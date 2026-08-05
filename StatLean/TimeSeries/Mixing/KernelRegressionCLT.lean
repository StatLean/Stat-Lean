import StatLean.TimeSeries.Mixing.Inequalities
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# CLT for kernel-localized sums under α-mixing (FY §2.6.4, Theorem 2.22)

The triangular-array CLT behind kernel regression with dependent data: for a strictly
stationary bivariate series `(X_t, e_t)` with `E(e|X) = 0`, the localized sums
`S_n(x) = Σ_{t=1}^n e_t W((X_t − x)/h_n)` satisfy
`(n h_n)^{-1/2} S_n(x) →d N(0, σ²(x) p(x) ∫ W²)` under (C1)–(C5). This is FY's
template for Theorem 6.3 (local-polynomial fitting) and the ch. 10 results.

**Conditions, as formalized.**
* (C1) joint strict stationarity (finite-dimensional-distribution form);
  `E(e_1 | X_1) = 0`, `E(e_1² | X_1) = σ²(X_1)`, `E|e_1|^δ < ∞` (δ > 2); the marginal
  `X_1` has a Lebesgue density `p`; `σ²`, `p` continuous at `x`, `p(x) > 0`.
* (C2) stated in its **operative integrated form**: uniformly in the lag `j ≠ 0`,
  `E[|e_0 e_j| g(X_0, X_j)] ≤ B · E[e_0²] · ∫∫ g` for nonnegative test functions `g` —
  this is exactly what FY's "conditional density of `(X_1, X_{j})` given `(e_1, e_j)`
  bounded uniformly in `j`" is used for (small-lag variance bound (2.76)), combined
  with Cauchy–Schwarz on `E|e_1 e_j|`.
* (C3) α-mixing of the bivariate series (`pairAlphaCoeff`) with
  `Σ_t t^λ α(t)^{1−2/δ} < ∞` for some `λ > 1 − 2/δ`.
* (C4) `W` bounded and measurable with `∫|W| < ∞`, `∫ W² < ∞`.
* (C5) **as corrected**: the printed display is inverted; we take the endorsed
  sufficient form `h_n → 0`, `h_n > 0`, `n h_n³ → ∞` (which implies the intended
  polynomial lower bound `n h_n^{(λ+2−2/δ)/(λ+2/δ)} → ∞`).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.4,
conditions (C1)–(C5) and Theorem 2.22 (pp. 76–77); proof §2.7.7 (pp. 85–87).
(`FY §2.6.4 Thm 2.22`.)

**Proof route (§2.7.7, for the closure session).** (a) variance asymptotics
(2.73)–(2.76): main diagonal term by continuity of `σ²·p` + substitution; small lags
`j ≤ m_n = [1/(h|log h|)]` by (C2'); large lags by Davydov (`abs_covariance_le_davydov`
with `p = q = δ`) + (C3). (b) Bernstein blocks `l_n = [√(nh)/log n]`,
`s_n = [(√(n/h) log n)^{(1−2/δ)/(λ+1)}]`; negligibility (2.79)–(2.81) via the variance
part. (c) truncation of `e` at level `L`; variance split (2.82)–(2.83).
(d) 4-term charFun telescope: truncation tail + Volkonskii–Rozanov
(`norm_integral_prod_sub_prod_integral_le`; `16(k_n − 1)α(s_n) → 0` by (2.78)) +
degenerate Lindeberg (`tendsto_charFun_rowSum_gaussian_of_uniformly_small`; the
truncated block summands have envelope `l_n L sup|W| / √(nh) → 0`) + `ν_L → ν`.
Sub-steps may be left as **named ledger-(a) debts** if the wave budget is hit.
[Print slips (recorded in the inventory): Term-1 of the telescope is missing a `½`
exponent; the final "(2.83)" should read "(2.84)".]

**Bibliographic comments.** Theorem 2.22 descends from Masry & Fan, *Local polynomial
estimation of regression functions for mixing processes* (Scand. J. Statist. 1997) and
Fan & Gijbels (1996) §6.5; the Bernstein-block scheme under (C3) follows Bosq (1998).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **bivariate past/future α-coefficient** (FY §2.6.4's mixing condition is on the
pair series `(X_t, e_t)`): α between `σ{(X_s, e_s) : s ≤ 0}` and
`σ{(X_s, e_s) : s ≥ n}`. -/
noncomputable def pairAlphaCoeff (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  alphaMixCoeff μ
    (⨆ s ∈ Set.Iic (0 : ℤ),
      MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance)
    (⨆ s ∈ Set.Ici (n : ℤ),
      MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance)

/-- **FY Theorem 2.22** (charFun form): under (C1)–(C5),
`(n h_n)^{-1/2} Σ_{t=1}^n e_t W((X_t − x)/h_n) →d N(0, σ²(x) p(x) ∫ W²)`. -/
theorem kernel_localized_clt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    -- (C1) USER-INPUT: joint strict stationarity (fdd form); FY (C1)
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ : ℝ} {x : ℝ}
    -- (C1) USER-INPUT: E(e₁ | X₁) = 0; FY (C1)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    -- (C1) USER-INPUT: E(e₁² | X₁) = σ²(X₁); FY (C1)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    -- (C1) USER-INPUT: δ-moment of the errors, δ > 2; FY (C1)
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- (C1) USER-INPUT: X₁ has Lebesgue density p; FY (C1)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    -- (C1) USER-INPUT: continuity at x and positivity; FY (C1)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- (C2) USER-INPUT: operative integrated form of the bounded conditional density
    -- of (X₁, X_j) given the errors; FY (C2), see the module docstring
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g →
      (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ}
    -- (C3) USER-INPUT: α-mixing rate of the pair series; FY (C3)
    (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ}
    -- (C4) USER-INPUT: bounded, integrable kernel with square-integrability; FY (C4)
    (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ}
    -- (C5) USER-INPUT (corrected form — printed display inverted): bandwidths
    -- positive, h → 0, n h³ → ∞; FY (C5)
    (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt ((n : ℝ) * h n))⁻¹ *
          ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume))) u)) := by
  sorry

end StatLean.TimeSeries
