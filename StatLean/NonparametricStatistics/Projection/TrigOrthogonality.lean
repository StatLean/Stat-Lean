import StatLean.NonparametricStatistics.Projection.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Orthonormality of the trigonometric system on [0, 1]

`∫₀¹ φⱼ(x)·φ_k(x) dx = δ_{jk}` for `j, k ≥ 1`, and the uniform bound `|φⱼ| ≤ √2`.

**Proof formalization notes.** Case-split on the parities and frequencies: the products reduce
by the product-to-sum identities (`Real.cos_mul_cos`-style, or directly
`2·cos a·cos b = cos(a−b) + cos(a+b)` etc.) to integrals of `cos(2πmx)` and `sin(2πmx)` over
`[0,1]`, which vanish for `m ≠ 0` (`integral_cos`, `integral_sin` with the `2πm` period) and
give the normalization `∫ cos² = ∫ sin² = 1/2` for equal frequencies (`integral_cos_sq`,
`integral_sin_sq`). The frequency arithmetic (`j/2 ± k/2 = 0` iff same-parity equal indices)
is the only bookkeeping.

**Bibliographic comments.** Classical Fourier analysis (J. Fourier, *Théorie analytique de la
chaleur*, 1822); the role of the trigonometric system in orthogonal series estimation goes
back to N. N. Čencov, *Soviet Math. Dokl.* **3** (1962), 1559–1562.
-/

open MeasureTheory intervalIntegral

namespace StatLean.NonparametricStatistics

/-- Uniform bound on the trigonometric system: `|φⱼ(x)| ≤ √2` for every `j` and `x`. -/
theorem trigBasis_abs_le (j : ℕ) (x : ℝ) : |trigBasis j x| ≤ Real.sqrt 2 := by
  sorry

/-- The trigonometric system is measurable in `x` for each index. -/
theorem trigBasis_measurable (j : ℕ) : Measurable (trigBasis j) := by
  sorry

/-- **Orthonormality of the trigonometric system on `[0,1]`**:
`∫₀¹ φⱼ·φ_k = 1` if `j = k` and `0` otherwise (indices `≥ 1`). -/
theorem trigBasis_orthonormal {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..1, trigBasis j x * trigBasis k x = if j = k then 1 else 0 := by
  sorry

end StatLean.NonparametricStatistics
