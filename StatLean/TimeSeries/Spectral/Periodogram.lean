import StatLean.TimeSeries.Spectral.DFT

/-!
# The periodogram (FY §2.4.2, Definition 2.8, Theorem 2.13)

`I_T(ω_k) = T⁻¹|Σ_t x_t e^{−itω_k}|² = |α_k|²` (FY Definition 2.8; no `2π` anywhere in
`I_T` — the density estimator is `I_T/2π`), the energy decomposition
`Σ_t x_t² = Σ_k I_T(ω_k)` (from discrete Parseval), and **FY Theorem 2.13** — the
deterministic identity `I_T(ω_k) = Σ_{|τ|<T} γ̂(τ) e^{−iτω_k}` for `k ≢ 0 (mod T)`,
where `γ̂` is the divisor-`T`, mean-corrected sample ACVF (FY eq. (2.23); §2.7.5 proof:
free mean-centering by root-of-unity sums, then reindex `τ = t − s`).

(FY Theorem 2.14 — the asymptotic distribution of the periodogram over a linear
process — is a batch-C target: its part (i) consumes the commissioned triangular-array
CLT; the statement will be added alongside `ForMathlib/Probability/TriangularCLT`.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.4.2,
Definition 2.8, Theorem 2.13 (pp. 62–63) and §2.7.5 (p. 81).
(`FY §2.4.2 Def 2.8, Thm 2.13; §2.7.5`.)

**Proof formalization notes.** Theorem 2.13 is per-data-vector (no probability); the
`k ≠ 0` hypothesis is the mod-`T` nondivisibility that kills the constant vector. The
sample-ACVF sum over `|τ| < T` is written as `τ = 0` plus two symmetric tails (our
`sampleACVF` takes `k : ℕ`; evenness of the sample ACVF is part of the statement's
bookkeeping).

**Bibliographic comments.** A. Schuster, "On the investigation of hidden periodicities"
(1898). The sample-ACVF identity is classical; FY follow Brockwell & Davis (1991),
Prop. 10.1.2.
-/

open Finset
open scoped Real

namespace StatLean.TimeSeries

/-- The **periodogram** (FY Definition 2.8): `I_T(k) = |α_k|²` at the `k`-th Fourier
frequency. -/
noncomputable def periodogram {T : ℕ} (x : Fin T → ℝ) (k : ℤ) : ℝ :=
  ‖dft x k‖ ^ 2

/-- **Energy decomposition** (FY §2.4.2, from eq. (2.52)):
`Σ_t x_t² = Σ_{k<T} I_T(k)`. -/
theorem sum_sq_eq_sum_periodogram {T : ℕ} (x : Fin T → ℝ) :
    ∑ t : Fin T, (x t) ^ 2 = ∑ k ∈ Finset.range T, periodogram x (k : ℤ) := by
  simpa only [periodogram] using sum_sq_eq_sum_normSq_dft x

/-- **FY Theorem 2.13** (proof §2.7.5): for a nonzero Fourier frequency, the
periodogram is the discrete Fourier transform of the sample autocovariances:
`I_T(ω_k) = γ̂(0) + Σ_{τ=1}^{T−1} γ̂(τ)·2cos(τω_k)`. (Real form of FY's
`Σ_{|τ|<T} γ̂(τ)e^{−iτω_k}`, using evenness of `γ̂`.) -/
theorem periodogram_eq_sampleACVF {T : ℕ} (hT : 0 < T) (x : Fin T → ℝ) {k : ℤ}
    -- USER-INPUT: k ≢ 0 (mod T) — FY's "k ≠ 0"; Thm 2.13 fails at the zero frequency
    (hk : ¬ ((T : ℤ) ∣ k)) :
    periodogram x k = sampleACVF x 0 +
      ∑ τ ∈ Finset.Icc 1 (T - 1), sampleACVF x τ * (2 * Real.cos (τ * fourierFreq T k)) := by
  sorry

/-- At the zero frequency the periodogram is `T · (sample mean)²` (FY §2.7.5 remark). -/
theorem periodogram_zero {T : ℕ} (x : Fin T → ℝ) :
    periodogram x 0 = T * sampleMean x ^ 2 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp [periodogram, dft]
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hfreq : fourierFreq T 0 = 0 := by simp [fourierFreq]
  have hdft : dft x 0 = (((Real.sqrt T)⁻¹ * ∑ t : Fin T, x t : ℝ) : ℂ) := by
    rw [dft, hfreq]
    push_cast
    simp
  rw [periodogram, hdft, Complex.norm_real, Real.norm_eq_abs, sq_abs, sampleMean, mul_pow,
    mul_pow, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (T : ℝ))]
  field_simp

end StatLean.TimeSeries
