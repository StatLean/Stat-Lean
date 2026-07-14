import StatLean.NonparametricStatistics.KernelDensity.Variance

/-!
# Integrated variance of the kernel density estimator

For **any** probability density `p` (no smoothness, no boundedness) and any square-integrable
kernel:
$$ \int \sigma^2(x)\,dx \;\le\; \frac{1}{nh}\int K^2(u)\,du. $$

The striking feature — emphasized in the classical treatment — is that no condition on `p`
whatsoever is required: integrating the pointwise second moment in `x` and applying
Tonelli–Fubini turns the density into its total mass `∫ p = 1`.

**Proof formalization notes.** `σ²(x) ≤ (nh²)⁻¹·E K²((X₁−x)/h)`; integrate in `x`, swap by
Tonelli (`lintegral_lintegral_swap`), and change variables `u = (z−x)/h` at fixed `z`
(translation invariance + scaling of Lebesgue measure), yielding
`(nh²)⁻¹·h·∫K²·∫p = (nh)⁻¹·∫K²`. Everything stays in `∫⁻`, so no integrability side
conditions arise.

**Bibliographic comments.** Classical mean-integrated-squared-error analysis: M. Rosenblatt,
*Ann. Math. Statist.* **27** (1956), 832–837; the exact-`L²` viewpoint was developed by
G. S. Watson and M. R. Leadbetter, "On the estimation of the probability density, I," *Ann.
Math. Statist.* **34** (1963), 480–491.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Integrated variance bound**: for any density `p` and square-integrable kernel,
`∫ σ²(x) dx ≤ (n·h)⁻¹·∫K²`. -/
theorem kde_integrated_variance_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity (no other condition on
    -- `p` is needed — the classical point of this bound)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical input
    (hK2 : Integrable fun u => (K u) ^ 2) :
    (∫⁻ x, kdeVarianceAt P X K h x)
      ≤ ENNReal.ofReal (((n : ℝ) * h)⁻¹ * ∫ u, (K u) ^ 2) := by
  sorry

end StatLean.NonparametricStatistics
