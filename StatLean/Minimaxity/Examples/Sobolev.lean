import StatLean.Minimaxity.Fano.LocalPacking
import StatLean.Minimaxity.Fano.YangBarron
import StatLean.Minimaxity.ForMathlib.Packing.SobolevEntropy

/-!
# Example: minimax risks for generalized Sobolev families (Wainwright Example 15.23)

For nonparametric regression over a smoothness-`α` Sobolev ellipsoid `ℱ_α`, the Yang–Barron method
(Lemma 15.21) with the metric entropy of `ℱ_α` (Example 5.12) gives the minimax risk in squared
`L²`-norm `≳ (σ²/n)^{2α/(2α+1)}` (Example 15.23). We state the local-packing form: a separation
`δₙ ≍ (σ²/n)^{α/(2α+1)}` with controlled pairwise KL yields, via `minimax_local_packing`, the rate
`δₙ² ≍ (σ²/n)^{2α/(2α+1)}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Example 15.23.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for Sobolev regression** (Wainwright Example 15.23): from a packing of the
smoothness-`α` Sobolev family with separation `δₙ = (σ²/n)^{α/(2α+1)}` and pairwise KL control,
`minimax_local_packing` gives a minimax risk (squared `L²`, encoded as `edist²`) of at least
`½ · (σ²/n)^{2α/(2α+1)}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Example 15.23. -/
theorem sobolev_regression_rate {ι 𝓧 Ω : Type*} [MeasurableSpace ι] [MeasurableSpace 𝓧]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] (n : ℕ) (hn : 1 ≤ n) (α σ : ℝ)
    (hα : 1 / 2 < α) (hσ : 0 < σ)
    (g : ι → Ω) (P : Kernel ι 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → ι) (hθ : Measurable θfam) (c : ℝ) (hM : 2 ≤ M)
    -- USER-INPUT: separation `δₙ = (σ²/n)^{α/(2α+1)}`; Wainwright §15.3.5, Example 15.23.
    (hsep : IsSeparatedFamily g θfam (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))))
    -- USER-INPUT: pairwise KL control (15.35a) for the Sobolev construction; Wainwright §15.3.5.
    (h35a : ∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
      ≤ ENNReal.ofReal (c ^ 2 * n * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2))
    -- USER-INPUT: packing cardinality (15.35b); Wainwright §15.3.5.
    (h35b : 2 * (c ^ 2 * n * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2 + Real.log 2) ≤ Real.log (M : ℝ)) :
    ENNReal.ofReal (2⁻¹ * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2) ≤ minimaxRiskDist (· ^ 2) g P := by
  have hx0 : (0 : ℝ) ≤ (σ ^ 2 / n) ^ (α / (2 * α + 1)) := by positivity
  have hδtoReal : (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))).toReal
      = (σ ^ 2 / n) ^ (α / (2 * α + 1)) := ENNReal.toReal_ofReal hx0
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have h35a' : ∀ j k, j ≠ k →
      klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * (n : ℝ) *
            (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))).toReal ^ 2) := by
    intro j k hjk; rw [hδtoReal]; exact h35a j k hjk
  have h35b' : 2 * (c ^ 2 * (n : ℝ) *
      (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))).toReal ^ 2 + Real.log 2)
      ≤ Real.log (M : ℝ) := by rw [hδtoReal]; exact h35b
  have key := minimax_local_packing (fun x : ℝ≥0∞ => x ^ 2) g P θfam hθ
    (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))) c (n : ℝ) hΦ hsep (by positivity) h35a' h35b'
  have harith : ENNReal.ofReal (2⁻¹ * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2)
      = 2⁻¹ * (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))) ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), ENNReal.ofReal_pow hx0,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [harith]
  exact key

end StatLean.Minimaxity
