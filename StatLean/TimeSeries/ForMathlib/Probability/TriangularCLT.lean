import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Lindeberg CLT for triangular (double) arrays

Row-wise independent triangular array `X_{n,1}, …, X_{n,k_n}` with zero means: if the
row variances converge (`Σᵢ Var X_{n,i} → σ²`) and the **Lindeberg condition** holds
(`∀ ε > 0, Σᵢ E[X_{n,i}² 1_{|X_{n,i}| ≥ ε}] → 0`), then the row sums are asymptotically
`N(0, σ²)` — stated through pointwise characteristic-function convergence
(Lévy-equivalent to convergence in distribution).

This is the "double-array" CLT that FY cites (Serfling 1980, p. 31) in the proof of
Theorem 2.14(i), and the assembly engine of the Bernstein-block CLTs (FY Theorems
2.21(ii) and 2.22). Mathlib (pin `5e932f97`) has the iid CLT
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) but no triangular-array
Lindeberg CLT, so we build it: the classical characteristic-function proof —
independence factorizes the row charFun into a product; second-order Taylor control of
each factor (`|E e^{iuX} − (1 − u²·Var X/2)| ≤ E min(|uX|³, 2(uX)²)`, split at `ε` by
Lindeberg); logarithm/product comparison against `e^{−u²σ²/2}`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003 — used for
Thm 2.14(i) (§2.7.6, citing R. J. Serfling, *Approximation Theorems of Mathematical
Statistics*, Wiley 1980, §1.9.3) and inside §2.7.7. (`FY §2.7.6`.)

**Bibliographic comments.** The Lindeberg condition and proof scheme are J. W. Lindeberg
(1922); the triangular-array formulation is standard from Loève and Billingsley
(*Probability and Measure*, Thm 27.2). The characteristic-function route implemented
here follows Billingsley's proof, replacing weak-convergence bookkeeping by pointwise
charFun convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Lindeberg CLT for triangular arrays** (row-wise independent, zero-mean; charFun
form). The Lindeberg sums use the set-integral over `{ε ≤ |X|}`. -/
theorem tendsto_charFun_rowSum_gaussian_of_lindeberg [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    -- USER-INPUT: row-wise independence; Lindeberg CLT
    (hindep : ∀ n, iIndepFun (X n) μ)
    -- USER-INPUT: zero means; Lindeberg CLT
    (hmean : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hL2 : ∀ n i, MemLp (X n i) 2 μ)
    {σ2 : ℝ}
    -- USER-INPUT: row-variance convergence; Lindeberg CLT
    (hvar : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 σ2))
    -- USER-INPUT: the Lindeberg condition; Lindeberg CLT
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map fun ω => ∑ i, X n i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

/-- Convenience corollary: a **uniformly negligible bounded** array (max bound → 0)
with converging row variances satisfies Lindeberg vacuously (eventually the Lindeberg
sets are empty) — the form used in the degenerate-Lindeberg step of FY §2.7.7. -/
theorem tendsto_charFun_rowSum_gaussian_of_uniformly_small [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) μ)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hL2 : ∀ n i, MemLp (X n i) 2 μ)
    {b : ℕ → ℝ}
    -- USER-INPUT: uniform envelope tending to zero; FY §2.7.7 degenerate Lindeberg
    (hbdd : ∀ n i, ∀ᵐ ω ∂μ, |X n i ω| ≤ b n)
    (hb0 : Tendsto b atTop (𝓝 0))
    {σ2 : ℝ}
    (hvar : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 σ2))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map fun ω => ∑ i, X n i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

end StatLean.TimeSeries
