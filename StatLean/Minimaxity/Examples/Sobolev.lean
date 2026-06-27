import StatLean.Minimaxity.Fano.YangBarron
import StatLean.Minimaxity.ForMathlib.Packing.SobolevEntropy

/-!
# Example: minimax risks for generalized Sobolev families (Wainwright Example 15.23)

For nonparametric regression `yᵢ = f*(xᵢ) + σ wᵢ` over a Sobolev ellipsoid `ℱ_α` of smoothness
`α > 1/2`, the Yang–Barron method (Lemma 15.21) with the metric entropy of `ℱ_α` (Example 5.12)
gives the minimax risk in squared `L²(ℙ)`-norm
```
inf_f̂ sup_{f ∈ ℱ_α} 𝔼[‖f̂ − f‖₂²] ≳ (σ²/n)^{2α/(2α+1)}        (Example 15.23).
```

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Example 15.23.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for Sobolev regression** (Wainwright Example 15.23): for the smoothness-`α`
Sobolev family `ℱ_α` and `n` i.i.d. observations with noise variance `σ²`, the minimax risk in
squared `L²`-norm is at least `c · (σ²/n)^{2α/(2α+1)}`, via the Yang–Barron bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Example 15.23. -/
theorem sobolev_regression_rate {ι 𝓧 Ω : Type*} [MeasurableSpace ι] [MeasurableSpace 𝓧]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] (n : ℕ) (hn : 1 ≤ n) (α σ : ℝ)
    (hα : 1 / 2 < α) (hσ : 0 < σ)
    (g : ι → Ω) (Pn : Kernel ι 𝓧) [IsMarkovKernel Pn]
    -- USER-INPUT: `g i` records `fᵢ ∈ ℱ_α` (squared `L²` loss as `edist`); Wainwright §15.3.5, Ex 15.23.
    (hclass : ∀ i, True) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * (σ ^ 2 / n) ^ (2 * α / (2 * α + 1)))
        ≤ minimaxRiskDist (· ^ 2) g Pn := by
  sorry

end StatLean.Minimaxity
