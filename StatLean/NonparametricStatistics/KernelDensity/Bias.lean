import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
import StatLean.NonparametricStatistics.SmoothnessClasses.HolderTaylor

/-!
# Pointwise bias of the kernel density estimator

For a density in the Hölder class `P(β, L)` and a kernel of order `ℓ = holderIndex β` with
finite `β`-moment:
$$ |b(x_0)| \;\le\; C_2\,h^{\beta}, \qquad C_2 = \frac{L}{\ell!}\int |u|^{\beta}|K(u)|\,du, $$
for all `x₀`, `h > 0`, `n ≥ 1` — non-asymptotic, dimension-free in `n`.

Contents:
* `integrable_kernel_mul_holder` — the *derived* integrability of `u ↦ K(u)·f(x₀ + uh)` for
  global Hölder `f` (never a hypothesis of the headline results);
* `abs_integral_kernel_taylor_le` — the deterministic core:
  `|∫ K(u)·f(x₀+uh) du − f(x₀)| ≤ C₂·h^β`;
* `kde_bias_abs_le` — the probabilistic statement for the estimator's bias.

**Proof formalization notes.** Write `∫K(u)f(x₀+uh)du − f(x₀) = ∫K(u)·(f(x₀+uh) − f(x₀))du`
using `∫K = 1`; insert the order-`ℓ` Taylor polynomial: the vanishing moments kill every term
`f⁽ʲ⁾(x₀)·hʲ·∫uʲK`, `1 ≤ j ≤ ℓ` (and the `j = 0` term cancels with `f(x₀)`), leaving the
Hölder–Taylor remainder, bounded pointwise by `(L/ℓ!)·|uh|^β`
(`MemHolder.taylor_remainder_abs_le`); integrating gives `C₂·h^β`. Integrability of every
intermediate integrand comes from the kernel's moment integrability and the polynomial-growth
envelope `MemHolder.abs_le_growth`. The probabilistic form composes with
`kdeMeanAt_eq_integral_kernel`.

**Bibliographic comments.** The bias computation with higher-order kernels is classical:
E. Parzen, *Ann. Math. Statist.* **33** (1962), 1065–1076; M. S. Bartlett, *Sankhyā Ser. A*
**25** (1963), 245–254.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Derived integrability**: for a global Hölder function `f` and a kernel of order
`ℓ = holderIndex β` with finite `β`-moment, `u ↦ K(u)·f(x₀ + u·h)` is integrable.
This discharges the integrability hypotheses of the law-transfer lemmas — it is never itself
a hypothesis of a headline theorem. -/
theorem integrable_kernel_mul_holder {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    {f K : ℝ → ℝ} (hf : MemHolder β L f)
    (hK : IsKernelOfOrder K (holderIndex β))
    (hKβ : Integrable fun u => |u| ^ β * |K u|)
    {h : ℝ} (hh : 0 < h) (x₀ : ℝ) :
    Integrable fun u => K u * f (x₀ + u * h) := by
  sorry

/-- **Deterministic bias core**: for global Hölder `f` and a kernel of order
`ℓ = holderIndex β` with finite `β`-moment,
`|∫ K(u)·f(x₀ + uh) du − f(x₀)| ≤ C₂·h^β` with `C₂ = kdeBiasConst β L K`. -/
theorem abs_integral_kernel_taylor_le {β L : ℝ}
    -- USER-INPUT: positive smoothness, nonnegative Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f K : ℝ → ℝ}
    -- USER-INPUT: `f` lies in the global Hölder class `Σ(β, L)`
    (hf : MemHolder β L f)
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition (cf. Parzen 1962)
    (hK : IsKernelOfOrder K (holderIndex β))
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|)
    {h : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h) (x₀ : ℝ) :
    |(∫ u, K u * f (x₀ + u * h)) - f x₀| ≤ kdeBiasConst β L K * h ^ β := by
  sorry

/-- **Pointwise bias bound for the kernel density estimator**: for `p ∈ P(β, L)`, kernel of
order `ℓ = holderIndex β` with finite `β`-moment, `n ≥ 1` and `h > 0`:
`|b(x₀)| ≤ C₂·h^β` with `C₂ = kdeBiasConst β L K`. -/
theorem kde_bias_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ} {x₀ : ℝ}
    {β L : ℝ}
    -- USER-INPUT: positive smoothness, nonnegative Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    -- LEAN-ONLY: nonempty sample; with `n = 0` the estimator degenerates to `0`
    (hn : 0 < n)
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- USER-INPUT: the density lies in the Hölder class `P(β, L)`
    (hp : IsHolderDensity β L p)
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition (cf. Parzen 1962)
    (hK : IsKernelOfOrder K (holderIndex β))
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|) :
    |kdeBiasAt P X K h p x₀| ≤ kdeBiasConst β L K * h ^ β := by
  sorry

end StatLean.NonparametricStatistics
