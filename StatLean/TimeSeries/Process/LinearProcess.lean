import StatLean.TimeSeries.Models.WhiteNoise

/-!
# Linear (MA(∞)) processes (FY §2.1.2, eq. (2.1))

The one-sided linear process `X_t = Σ_{j≥0} ψ_j ε_{t−j}` with absolutely summable
coefficients over white noise: well-definedness (`L²` convergence of the partial sums),
existence, stationarity with the autocovariance formula
`γ(k) = σ² Σ_{j≥0} ψ_j ψ_{j+|k|}` (FY eq. (2.2)), strict stationarity under i.i.d.
innovations, and (as an allowed debt in this wave) almost-sure convergence under
independence (FY cites Chow & Teicher 1997, Cor. 3 p. 117).

`IsLinearProcessOf ψ X ε μ` says the partial sums converge to `X t` in `L²`
(`eLpNorm … 2 μ → 0`) at every time — the convergence mode FY works with. (The
*two-sided* linear process of FY Theorem 2.8/2.14 will generalize this in batch B/C.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.2,
eqs. (2.1)–(2.2) (pp. 30–31). (`FY §2.1.2 eq. (2.1)–(2.2)`.)

**Proof formalization notes.** Existence: the partial sums are Cauchy in `L²` by
`ℓ¹ ⊆ ℓ²` of the coefficients and WN orthogonality; completeness of `L²` provides a
limit, chosen measurably per `t`. The ACVF formula interchanges `cov` with the `L²`
limits (continuity of the inner product) and collapses the double series by
uncorrelatedness. Strict stationarity under i.i.d. innovations transports the
finite-dimensional laws of the partial sums (each a fixed measurable function of a
shift of the i.i.d. family) to the a.e./in-measure limit.

**Bibliographic comments.** Infinite moving averages originate with E. Slutsky (1927)
and H. Wold (1938); the `L²` theory is the Wiener–Kolmogorov era's; the almost-sure
convergence of independent series is Kolmogorov's three-series/maximal-inequality circle
(FY cite Y. S. Chow and H. Teicher, *Probability Theory*, 3rd ed., Springer, 1997).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `X` is the **linear process** with coefficients `ψ` over the noise `ε` (FY eq.
(2.1)): at every time the `L²` distance from the partial sums vanishes,
`‖X_t − Σ_{j<N} ψ_j ε_{t−j}‖_{L²(μ)} → 0`. -/
def IsLinearProcessOf (ψ : ℕ → ℝ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N => eLpNorm
      (fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ)
    atTop (𝓝 0)

/-- **Existence** (FY §2.1.2): over white noise, absolutely summable coefficients define
a linear process (`L²`-limits of the partial sums, chosen measurably). -/
theorem exists_isLinearProcessOf [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: absolutely summable coefficients; FY eq. (2.1)
    (hψ : Summable fun j => |ψ j|)
    -- USER-INPUT: white-noise innovations; FY eq. (2.1)
    (hε : IsWhiteNoise ε σ2 μ) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ IsLinearProcessOf ψ X ε μ := by
  sorry

/-- Marginals of a linear process are in `L²`. -/
theorem IsLinearProcessOf.memLp [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    -- LEAN-ONLY: measurability of the limits; supplied by `exists_isLinearProcessOf`
    (hmeas : ∀ t, Measurable (X t)) (t : ℤ) : MemLp (X t) 2 μ := by
  sorry

/-- **Stationarity + the ACVF formula** (FY §2.1.2, eq. (2.2)): a linear process over
white noise is weakly stationary with `γ(k) = σ² Σ_{j≥0} ψ_j ψ_{j+|k|}`. -/
theorem IsLinearProcessOf.isStationary [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) :
    IsStationary X μ ∧
      ∀ k : ℤ, acvf X μ k = σ2 * ∑' j : ℕ, ψ j * ψ (j + k.natAbs) := by
  sorry

/-- **Strict stationarity under i.i.d. innovations** (FY §2.1.2, asserted): a linear
process over i.i.d. noise is strictly stationary. -/
theorem IsLinearProcessOf.isStrictlyStationary [IsProbabilityMeasure μ] {ψ : ℕ → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsIIDNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) :
    IsStrictlyStationary X μ := by
  sorry

/-- **Almost-sure convergence under independence** — ALLOWED DEBT in wave A2 (FY cites
Chow & Teicher 1997, Cor. 3 p. 117; route: Kolmogorov maximal inequality / martingale
convergence on the partial sums). -/
theorem IsLinearProcessOf.ae_tendsto [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsIIDNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) atTop (𝓝 (X t ω)) := by
  sorry

end StatLean.TimeSeries
