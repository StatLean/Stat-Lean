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
