import StatLean.NonparametricStatistics.KernelDensity.IntegratedVariance
import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral

/-!
# Exact asymptotics of the integrated variance

The two-sided refinement of the integrated variance bound: for a square-integrable density,
$$ \frac{1}{nh}\int K^2 - \frac{1}{n}\Bigl(\int |K|\Bigr)^2\!\!\int p^2
   \;\le\; \int \sigma^2(x)\,dx \;\le\; \frac{1}{nh}\int K^2 . $$
The correction term is `O(1/n)`, hence negligible against the main term `(nh)⁻¹∫K²` as
`h → 0` — this is the variance half of the exact asymptotic MISE.

**Proof formalization notes.** The exact identity is
`∫σ² = (nh²)⁻¹(h∫K² − ∫(E K((X−x)/h))² dx)`; the subtracted term is the squared `L²` norm of
the convolution-type mean, bounded by Young/Minkowski
(`‖|K|_h ⋆ p‖₂ ≤ ‖|K|_h‖₁·‖p‖₂ = ∫|K|·‖p‖₂`, via `lintegral_lintegral_sq_rpow_le`), giving
the correction `n⁻¹·(∫|K|)²·∫p²`. Requires `p ∈ L²` — supplied as a hypothesis
(`MemLp p 2`); see the batch ledger for its status (derivable in principle for the densities
of the exact-MISE theorem, kept as a documented input here).

**Bibliographic comments.** G. S. Watson and M. R. Leadbetter, "On the estimation of the
probability density, I," *Ann. Math. Statist.* **34** (1963), 480–491.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Integrated variance, exact lower bound**: for a square-integrable density,
`(nh)⁻¹∫K² − n⁻¹(∫|K|)²·∫p² ≤ ∫ σ²(x) dx`. Together with
`kde_integrated_variance_le` this pins the integrated variance to `(nh)⁻¹∫K²` up to `O(1/n)`. -/
theorem kde_integrated_variance_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    -- LEAN-ONLY: nonempty sample and positive bandwidth; standard side conditions
    (hn : 0 < n) (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability of the observations; standard regularity
    (hX : ∀ i, Measurable (X i))
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    -- USER-INPUT: square-integrable density; input of the exact variance asymptotics
    -- (documented: derivable for the exact-MISE densities, kept as an input here)
    (hp2 : MemLp p 2 volume)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hK : Measurable K)
    -- USER-INPUT: integrable and square-integrable kernel; classical inputs
    (hK1 : Integrable K) (hK2 : Integrable fun u => (K u) ^ 2) :
    ENNReal.ofReal (((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
        - (n : ℝ)⁻¹ * (∫ u, |K u|) ^ 2 * ∫ x, (p x) ^ 2)
      ≤ ∫⁻ x, kdeVarianceAt P X K h x := by
  sorry

end StatLean.NonparametricStatistics
