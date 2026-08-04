import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.Process.Autocovariance

/-!
# White noise — basic theory (FY §1.3.1, §2.2.1)

The ch. 1 claims about the noise classes: i.i.d. noise is white noise ("easy to see",
FY §1.3.1); white noise is (weakly) stationary with autocovariance `γ(k) = σ² δ_{k0}`
and flat ACF; and among zero-mean stationary processes, white noise is characterized by
the vanishing of all nonzero-lag autocorrelations (FY §2.2.1, p. 40).

(The remaining §1.3.1 claim — a *Gaussian* white noise is i.i.d. normal — needs the
Gaussian-process layer and is scheduled with `Stationarity/Gaussian.lean` in batch B.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §1.3.1
(p. 10) and §2.2.1 (p. 40). (`FY §1.3.1; §2.2.1`.)

**Proof formalization notes.** `IsIIDNoise.isWhiteNoise` transports moments along
`IdentDistrib` and gets uncorrelatedness from independence (`IndepFun` of distinct
coordinates via `iIndepFun`, then covariance of independent integrable variables
vanishes). The characterization keeps the book's implicit zero-mean hypothesis explicit.

**Bibliographic comments.** White noise as the elementary building block of linear time
series is due to E. Slutsky ("The summation of random causes as the source of cyclic
processes", 1927/1937) and H. Wold (1938); the "innovation" terminology is Wiener–
Kolmogorov prediction theory.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℤ → Ω → ℝ} {σ2 : ℝ}

/-- **IID ⊆ WN** (FY §1.3.1, "easy to see"): i.i.d. noise is white noise. -/
theorem IsIIDNoise.isWhiteNoise [IsProbabilityMeasure μ] (h : IsIIDNoise ε σ2 μ) :
    IsWhiteNoise ε σ2 μ := by
  sorry

/-- White noise is weakly stationary. -/
theorem IsWhiteNoise.isStationary [IsProbabilityMeasure μ] (h : IsWhiteNoise ε σ2 μ) :
    IsStationary ε μ := by
  sorry

/-- The autocovariance of white noise: `γ(k) = σ² δ_{k0}`. -/
theorem IsWhiteNoise.acvf_eq [IsProbabilityMeasure μ] (h : IsWhiteNoise ε σ2 μ)
    (k : ℤ) : acvf ε μ k = if k = 0 then σ2 else 0 := by
  sorry

/-- **Characterization** (FY §2.2.1, p. 40): a zero-mean stationary process is white
noise (with its own variance) iff all nonzero-lag autocovariances vanish. -/
theorem isWhiteNoise_iff_acvf [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: zero mean (implicit in FY's WN comparison); FY §2.2.1 p. 40
    (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0) :
    IsWhiteNoise X (acvf X μ 0) μ ↔ ∀ k : ℤ, k ≠ 0 → acvf X μ k = 0 := by
  sorry

end StatLean.TimeSeries
