import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pointwise variance of the kernel density estimator

For an i.i.d. sample from a density bounded by `pmax` and a square-integrable kernel:
$$ \sigma^2(x_0) \;\le\; \frac{C_1}{n h}, \qquad C_1 = p_{\max}\int K^2(u)\,du, $$
for **any** `x₀`, `h > 0`, `n` — a fully non-asymptotic bound. Also provided: the estimator is
square-integrable under these hypotheses, and the exact bias–variance decomposition of the
pointwise mean squared error.

**Proof formalization notes.** Write `p̂ₙ(x₀) = (nh)⁻¹ ∑ ηᵢ + E` with
`ηᵢ = K((Xᵢ−x₀)/h) − E K((Xᵢ−x₀)/h)` i.i.d. centered; independence gives
`Var(p̂ₙ(x₀)) = (nh²)⁻¹·n⁻¹·…` — concretely `Mathlib`'s `IndepFun.variance_sum` after
establishing `MemLp 2` of each summand from
`E K² = ∫ K²((z−x₀)/h)·p(z) dz ≤ pmax·h·∫K²` (law transfer + change of variables). The `ℝ≥0∞`
definition `kdeVarianceAt` matches the Bochner variance under `MemLp 2`
(`kdeVarianceAt_eq_ofReal_variance`); the decomposition needs the same `MemLp 2`.
Degenerate `n = 0` makes the estimator `0` and both sides vacuous-but-true.

**Bibliographic comments.** The variance computation is the classical opening move of kernel
density estimation: M. Rosenblatt, *Ann. Math. Statist.* **27** (1956), 832–837; E. Parzen,
*Ann. Math. Statist.* **33** (1962), 1065–1076.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The kernel estimator at a point is square-integrable when the sampled density is bounded
and the kernel is measurable and square-integrable. -/
theorem kde_memLp_two {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h pmax : ℝ} {x : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- USER-INPUT: the density is bounded by `pmax`; classical variance-bound input
    (hbdd : ∀ x, p x ≤ pmax)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical variance-bound input
    (hK2 : Integrable fun u => (K u) ^ 2) :
    MemLp (fun ω => kde X K h ω x) 2 P := by
  sorry

/-- Under square-integrability, the `ℝ≥0∞`-valued variance functional is the Bochner
variance. -/
theorem kdeVarianceAt_eq_ofReal_variance {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ → ℝ}
    {h : ℝ} {x : ℝ}
    (hL2 : MemLp (fun ω => kde X K h ω x) 2 P) :
    kdeVarianceAt P X K h x
      = ENNReal.ofReal (variance (fun ω => kde X K h ω x) P) := by
  sorry

/-- **Bias–variance decomposition of the pointwise MSE** (exact, under square-integrability):
`MSE(x) = b(x)² + σ²(x)`. -/
theorem kdeMseAt_eq_bias_sq_add_variance {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ → ℝ}
    {h : ℝ} {p : ℝ → ℝ} {x : ℝ}
    (hL2 : MemLp (fun ω => kde X K h ω x) 2 P) :
    kdeMseAt P X K h p x
      = ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2) + kdeVarianceAt P X K h x := by
  sorry

/-- **Pointwise variance bound for the kernel density estimator**: for any `x₀`, `h > 0`, `n`,
`σ²(x₀) ≤ C₁/(n·h)` with the explicit constant `C₁ = pmax·∫K²`. -/
theorem kde_variance_le {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h pmax : ℝ} {x₀ : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- USER-INPUT: the density is bounded by `pmax`; classical variance-bound input
    (hbdd : ∀ x, p x ≤ pmax)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical variance-bound input
    (hK2 : Integrable fun u => (K u) ^ 2) :
    kdeVarianceAt P X K h x₀
      ≤ ENNReal.ofReal (kdeVarianceConst K pmax / ((n : ℝ) * h)) := by
  sorry

end StatLean.NonparametricStatistics
