import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Positive semidefinite sequences on ℤ

A real sequence `γ : ℤ → ℝ` is **positive semidefinite** when every quadratic form
`Σᵢⱼ aᵢ aⱼ γ(tᵢ − tⱼ)` built from finitely many time points is nonnegative (FY
eq. (2.17)). This is the characterizing property of autocovariance functions
(FY Theorem 2.7, `Process/Autocovariance.lean`) and the sole input to the Herglotz
theorem (FY Theorem 2.10, `ForMathlib/Fourier/HerglotzBochner.lean`).

Basic consequences stated here: `γ(0) ≥ 0`; `|γ(k)| ≤ γ(0)` for even `γ`; and the
upgrade from real to complex coefficient vectors (for even `γ` the Hermitian quadratic
form `Σᵢⱼ cᵢ c̄ⱼ γ(tᵢ − tⱼ)` is real and nonnegative) — the positivity engine behind the
Fejér construction.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.1,
eq. (2.17) (p. 40). (`FY §2.2.1 eq. (2.17)`.)

**Proof formalization notes.** The complex upgrade needs evenness: writing `c = a + ib`,
the imaginary part of the Hermitian form vanishes by the symmetry
`γ(tᵢ − tⱼ) = γ(tⱼ − tᵢ)`, and the real part splits as the sum of the two real quadratic
forms in `a` and `b`.

**Bibliographic comments.** Nonnegative-definite functions on groups and their harmonic
analysis go back to C. Carathéodory, O. Toeplitz and G. Herglotz (1911) for `ℤ`, and to
S. Bochner (1932) for `ℝ`; the role as the exact characterization of covariance
functions is due to A. Ya. Khinchin (1934).
-/

namespace StatLean.TimeSeries

/-- **Positive semidefinite sequence** on `ℤ` (FY eq. (2.17)): every finite real
quadratic form `Σᵢⱼ aᵢ aⱼ γ(tᵢ − tⱼ)` is nonnegative. -/
def IsPosSemidefSeq (γ : ℤ → ℝ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℤ) (a : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, a i * a j * γ (t i - t j)

namespace IsPosSemidefSeq

variable {γ : ℤ → ℝ}

/-- `γ(0) ≥ 0` for a positive semidefinite sequence (take `n = 1`, `a = 1`). -/
theorem nonneg_zero (h : IsPosSemidefSeq γ) : 0 ≤ γ 0 := by
  sorry

/-- `|γ(k)| ≤ γ(0)` for an even positive semidefinite sequence (the `2 × 2` quadratic
forms with coefficient vectors `(1, 1)` and `(1, -1)`). -/
theorem abs_le_of_even (h : IsPosSemidefSeq γ) (heven : ∀ k, γ (-k) = γ k) (k : ℤ) :
    |γ k| ≤ γ 0 := by
  sorry

/-- Complex upgrade, imaginary part: for even `γ`, the Hermitian quadratic form
`Σᵢⱼ cᵢ c̄ⱼ γ(tᵢ − tⱼ)` is real. -/
theorem complex_sum_im (_h : IsPosSemidefSeq γ) (heven : ∀ k, γ (-k) = γ k)
    {n : ℕ} (t : Fin n → ℤ) (c : Fin n → ℂ) :
    (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (γ (t i - t j) : ℂ)).im = 0 := by
  sorry

/-- Complex upgrade, real part: for an even positive semidefinite `γ`, the Hermitian
quadratic form `Σᵢⱼ cᵢ c̄ⱼ γ(tᵢ − tⱼ)` is nonnegative. -/
theorem complex_sum_re_nonneg (h : IsPosSemidefSeq γ) (heven : ∀ k, γ (-k) = γ k)
    {n : ℕ} (t : Fin n → ℤ) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (γ (t i - t j) : ℂ)).re := by
  sorry

end IsPosSemidefSeq

end StatLean.TimeSeries
