import StatLean.TimeSeries.Spectral.SpectralDensity

/-!
# Linear filters and the input–output spectral relation (FY §2.3.3, Theorem 2.12)

**Definition 2.7** (two-sided linear filter with `ℓ¹` coefficients, as an `L²`-limit —
the convergence mode FY leaves implicit), the **transfer function**
`Γ(λ) = Σ_{k ∈ ℤ} φ_k e^{−ikλ}`, and **FY Theorem 2.12** with the inventory's
hypothesis-discipline upgrades: for a stationary input with summable ACVF and an `ℓ¹`
filter, the output is stationary (derived, not assumed), its ACVF is the double
convolution `γ_X(k) = Σ_{j,l} φ_j φ_l γ_Y(k + j − l)` and is summable (derived — FY
assumes it), and the spectral densities satisfy `g_X = |Γ|² g_Y` pointwise.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.3,
Definition 2.7 (eqs. (2.41)–(2.42)), Theorem 2.12 with in-text proof (pp. 55–56).
(`FY §2.3.3 Def 2.7, Thm 2.12`.)

**Proof formalization notes.** Well-definedness (existence of the `L²`-limits) mirrors
the one-sided `Process/LinearProcess.lean` development with two-sided symmetric partial
sums `Σ_{|k| ≤ N}`; the ACVF convolution passes `L²`-continuity of covariance through
the double series (Fubini for absolutely convergent double sums,
`Summable.tsum_comm`-family); the density identity is the triple-series rearrangement of
FY's proof, executed on the series side of `spectralDensityOf`.

**Bibliographic comments.** Linear filtering of stationary processes is classical
Wiener–Kolmogorov theory; FY follow Brockwell & Davis (1991), Thm 4.4.1.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Two-sided linear filter** (FY Definition 2.7, eq. (2.41)): `X_t = Σ_{k ∈ ℤ} φ_k
Y_{t−k}` as an `L²`-limit of the symmetric partial sums. -/
def IsFilteredBy (X Y : ℤ → Ω → ℝ) (φ : ℤ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N : ℕ => eLpNorm
      (fun ω => X t ω - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ k * Y (t - k) ω) 2 μ)
    atTop (nhds 0)

/-- The **transfer function** `Γ(λ) = Σ_{k ∈ ℤ} φ_k e^{−ikλ}` (FY §2.3.3; junk when
`φ ∉ ℓ¹` by the `tsum` convention). -/
noncomputable def transferFun (φ : ℤ → ℝ) (l : AddCircle (2 * π)) : ℂ :=
  ∑' k : ℤ, (φ k : ℂ) * fourier (-k) l

/-- **Existence of the filtered process** (the well-definedness FY glosses): an `ℓ¹`
filter applied to a weakly stationary input admits an `L²` output. -/
theorem exists_isFilteredBy [IsProbabilityMeasure μ] {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hmeas : ∀ t, Measurable (Y t)) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ IsFilteredBy X Y φ μ := by
  sorry

/-- **FY Theorem 2.12, stationarity + ACVF convolution** (output stationarity and the
double-convolution formula, both *derived* — FY assumes the former and glosses the
latter): `γ_X(k) = Σ'_j Σ'_l φ_j φ_l γ_Y(k + j − l)`. -/
theorem IsFilteredBy.isStationary [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t)) :
    IsStationary X μ ∧
      ∀ k : ℤ, acvf X μ k = ∑' j : ℤ, ∑' l : ℤ, φ j * φ l * acvf Y μ (k + j - l) := by
  sorry

/-- Summability of the output ACVF (derived; FY assumes it): `ℓ¹ ∗ ℓ¹ ∗ ℓ¹`. -/
theorem IsFilteredBy.hasSummableACVF [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hYsum : HasSummableACVF Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t)) :
    HasSummableACVF X μ := by
  sorry

/-- **FY Theorem 2.12 (spectral form)**: `g_X(λ) = |Γ(λ)|² · g_Y(λ)`. -/
theorem IsFilteredBy.spectralDensityOf_eq [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hYsum : HasSummableACVF Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l = ‖transferFun φ l‖ ^ 2 * spectralDensityOf Y μ l := by
  sorry

end StatLean.TimeSeries
