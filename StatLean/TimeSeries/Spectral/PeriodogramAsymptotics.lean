import StatLean.TimeSeries.Spectral.Periodogram
import StatLean.TimeSeries.Spectral.LinearFilter
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import StatLean.TimeSeries.Models.WhiteNoise

/-!
# Periodogram asymptotics (FY §2.4.2, Theorem 2.14)

For a two-sided linear process `X_t = Σ_{j∈ℤ} a_j ε_{t−j}` with iid `(0, σ²)`
innovations and `Σ|a_j| < ∞`, writing `n = [(T−1)/2]` and, for `1 ≤ k ≤ n`,

* `ξ_{2k−1} = (2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t cos(t ω_k)` (`dftNoiseCos`),
* `ξ_{2k} = (2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t sin(t ω_k)` (`dftNoiseSin`):

**Theorem 2.14.**
(i) every fixed finite linear combination `Σ_j c_j ξ_{k_j}` (distinct indices) is
asymptotically `N(0, Σ_j c_j²)` — proved via the exact discrete trigonometric
orthogonality (variance is exactly `Σ c_j²` up to `O(1/T)`) and the double-array
Lindeberg CLT (`TriangularCLT`);
(ii) `I_T(ω_k) = 2π g(ω_k) (ξ_{2k−1}² + ξ_{2k}²)/2 + R_T(ω_k)` with
`max_{1≤k≤n} E|R_T(ω_k)| → 0` — via the DFT-of-filter factorization
`α_k = a(e^{−iω_k}) α_{k,ε} + Y_T(ω_k)` and the uniform L² edge-effect bound
(FY eq. (2.72), Cauchy–Schwarz against the `ℓ¹` tail of `a`).

Consequence recorded in FY's text (not separately stated here): the normalized
ordinates `I_T(ω_k)/(2π g(ω_k))` are asymptotically iid `Exp(1)` — this is (i) + (ii) +
continuous mapping, deferred until a consumer needs it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.4.2,
Theorem 2.14 (p. 63); proof §2.7.6 (pp. 83–85), citing Serfling (1980) p. 31 for the
double-array CLT. (`FY §2.4.2 Thm 2.14`.)

**Proof formalization notes.**
* The frequencies use `fourierFreq T k = 2πk/T` and the time index `t = 1, …, T` as in
  `Spectral/DFT.lean` (whose exponential-orthogonality lemmas drive the exact variance
  computation in (i)).
* In (ii) the remainder bound is uniform over `k ≤ n`: stated with an explicit
  vanishing envelope sequence `b : ℕ → ℝ` rather than a `Finset.sup`, avoiding junk
  when the frequency window is empty (`T ≤ 2`).
* The spectral density `g` is `spectralDensityOf X μ` at the circle point
  `(fourierFreq T k : AddCircle (2π))`; summability of the ACVF (needed for `g` to be
  the honest density) is derived from `Σ|a_j| < ∞` via the filter theory
  (`IsFilteredBy.hasSummableACVF` with white-noise input).

**Bibliographic comments.** Theorem 2.14 descends from Brockwell & Davis (1991),
Prop 10.3.1–Thm 10.3.2; the χ²₂-limit picture of periodogram ordinates goes back to
Fisher (1929) and Bartlett (1950).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The normalized **cosine noise sum** `ξ_{2k−1}` (FY §2.7.6):
`(2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t cos(t ω_k)`; junk when `σ² ≤ 0` or `T = 0`. -/
noncomputable def dftNoiseCos (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 / T) / Real.sqrt σ2 *
    ∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k)

/-- The normalized **sine noise sum** `ξ_{2k}` (FY §2.7.6). -/
noncomputable def dftNoiseSin (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 / T) / Real.sqrt σ2 *
    ∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k)

/-- The interleaved family: `ξ-index 2k−1 ↦ cos` at frequency `k`, `2k ↦ sin` at
frequency `k` (FY's numbering; `j ≥ 1`). -/
noncomputable def dftNoiseXi (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (j : ℕ) : Ω → ℝ :=
  if j % 2 = 1 then dftNoiseCos ε σ2 T ((j + 1) / 2) else dftNoiseSin ε σ2 T (j / 2)

/-- **FY Theorem 2.14(i)**: any fixed finite linear combination of distinct
`ξ`-coordinates is asymptotically `N(0, Σ c²)` (charFun form). The index selection
`κsel` picks `m` distinct `ξ`-indices; the indices are fixed while `T → ∞`. -/
theorem dftNoiseXi_clt [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: iid(0, σ²) innovations; FY Thm 2.14
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    {m : ℕ} (c : Fin m → ℝ)
    -- USER-INPUT: distinct ξ-indices, all ≥ 1; FY Thm 2.14(i)
    (κsel : Fin m → ℕ) (hinj : Function.Injective κsel) (h1 : ∀ i, 1 ≤ κsel i)
    (u : ℝ) :
    Tendsto (fun T : ℕ =>
        charFun (μ.map fun ω => ∑ i, c i * dftNoiseXi ε σ2 T (κsel i) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (∑ i, c i ^ 2))) u)) := by
  sorry

/-- **FY Theorem 2.14(ii)**: for the two-sided linear process, uniformly over the
Fourier frequencies `1 ≤ k ≤ [(T−1)/2]`, the periodogram ordinate is the rescaled
χ²₂-type quadratic form of the noise trigonometric sums up to an `L¹`-negligible
remainder:
`E |I_T(ω_k) − 2π g(ω_k) (ξ_{2k−1}² + ξ_{2k}²)/2| ≤ b_T → 0`. -/
theorem periodogram_eq_scaled_chi2_approx [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: iid(0, σ²) innovations; FY Thm 2.14
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: absolutely summable two-sided coefficients; FY Thm 2.14
    (ha : Summable fun j : ℤ => |a j|)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: two-sided linear representation (FY eq. (2.24), zero mean),
    -- definitionally `IsFilteredBy X ε a μ`
    (hfil : IsFilteredBy X ε a μ) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ T k : ℕ, 1 ≤ k → k ≤ (T - 1) / 2 →
        ∫ ω, |periodogram (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k
            - 2 * π * spectralDensityOf X μ ((fourierFreq T k : ℝ) : AddCircle (2 * π))
              * ((dftNoiseCos ε σ2 T k ω) ^ 2 + (dftNoiseSin ε σ2 T k ω) ^ 2) / 2|
          ∂μ ≤ b T := by
  sorry

end StatLean.TimeSeries
