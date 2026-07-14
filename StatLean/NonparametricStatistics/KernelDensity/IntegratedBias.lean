import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
import StatLean.NonparametricStatistics.SmoothnessClasses.NikolskiTaylor

/-!
# Integrated squared bias of the kernel density estimator

For a density in the Nikol'skii class `P_H(β, L)` and a kernel of order `ℓ = holderIndex β`
with finite `β`-moment:
$$ \int b^2(x)\,dx \;\le\; C_2^2\,h^{2\beta}, \qquad
   C_2 = \frac{L}{\ell!}\int|u|^{\beta}|K(u)|\,du $$
— the same constant as the pointwise bias bound, now in integrated form.

**Proof formalization notes.** For a.e. `x` (Tonelli gives `∫∫|K(u)|·p(x+uh)·du·dx =
∫|K| < ∞`, hence a.e.-`x` integrability), the bias equals
`∫K(u)·(p(x+uh) − ∑_{j≤ℓ} p⁽ʲ⁾(x)(uh)ʲ/j!)du` after moment cancellation. The `L²(dx)`-norm is
pulled inside the `u`-integral by the generalized Minkowski inequality
(`lintegral_lintegral_sq_rpow_le`), and each slice is bounded by the Nikol'skii–Taylor
remainder bound (`MemNikolski.lintegral_sq_remainder_le`), giving
`‖b‖₂ ≤ ∫|K(u)|·(L/ℓ!)|uh|^β du = C₂·h^β`. On the junk set of `x` where the Bochner mean is
`0`, the lower Lebesgue integral is unaffected (null set). Everything stays in `∫⁻`.

**Bibliographic comments.** The Nikol'skii-class integrated bias computation is the classical
route to MISE rates; cf. S. M. Nikol'skii, *Approximation of Functions of Several Variables
and Imbedding Theorems* (Springer, 1975) for the class, and G. S. Watson and
M. R. Leadbetter, *Ann. Math. Statist.* **34** (1963), 480–491, for the `L²` analysis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Integrated squared bias bound**: for `p ∈ P_H(β, L)`, kernel of order
`ℓ = holderIndex β` with finite `β`-moment, `n ≥ 1`, `h > 0`:
`∫ b²(x) dx ≤ C₂²·h^{2β}` with `C₂ = kdeBiasConst β L K`. -/
theorem kde_integrated_sq_bias_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ} {β L : ℝ}
    -- USER-INPUT: positive smoothness, nonnegative constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    -- LEAN-ONLY: nonempty sample; with `n = 0` the estimator degenerates
    (hn : 0 < n)
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the density lies in the Nikol'skii class `P_H(β, L)`
    (hp : IsNikolskiDensity β L p)
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition
    (hK : IsKernelOfOrder K (holderIndex β))
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|) :
    (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
      ≤ ENNReal.ofReal ((kdeBiasConst β L K) ^ 2 * h ^ (2 * β)) := by
  sorry

end StatLean.NonparametricStatistics
