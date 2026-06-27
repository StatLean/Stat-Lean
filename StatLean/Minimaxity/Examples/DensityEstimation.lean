import StatLean.Minimaxity.Fano.LocalPacking
import StatLean.Minimaxity.ForMathlib.Packing.HammingPacking

/-!
# Example: minimax risk for density estimation (Wainwright Examples 15.15, 15.22)

Estimating a twice-smooth density `f ∈ ℱ₂` in the squared Hellinger metric, from `n` i.i.d. samples,
has minimax risk `≳ n^{-4/5}` (Examples 15.15, 15.22). We state the Fano local-packing route
(Example 15.15): a Hamming-separated subfamily of perturbed densities with separation `δₙ ≍ n^{-2/5}`
and controlled pairwise KL yields, via `minimax_local_packing`, the rate `δₙ² ≍ n^{-4/5}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3, Examples 15.15, 15.22.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for density estimation in Hellinger distance** (Wainwright Example 15.15): for a
local packing of the twice-smooth density class with separation `δₙ = n^{-2/5}` and pairwise KL
control (the perturbed-density / Hamming construction), `minimax_local_packing` gives a minimax
risk (squared Hellinger, encoded as `edist²`) of at least `½ · n^{-4/5}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3, Example 15.15. -/
theorem density_estimation_hellinger_rate {ι 𝓧 Ω : Type*} [MeasurableSpace ι] [MeasurableSpace 𝓧]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] (n : ℕ) (hn : 1 ≤ n)
    (g : ι → Ω) (P : Kernel ι 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → ι) (hθ : Measurable θfam) (c : ℝ) (hM : 2 ≤ M)
    -- USER-INPUT: a Hamming-separated subfamily with separation `δₙ = n^{-2/5}`; Wainwright §15.3, Ex 15.15.
    (hsep : IsSeparatedFamily g θfam (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))))
    -- USER-INPUT: pairwise KL control (15.35a) for the perturbed-density construction; Wainwright §15.3.
    (h35a : ∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
      ≤ ENNReal.ofReal (c ^ 2 * n * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2))
    -- USER-INPUT: packing cardinality (15.35b); Wainwright §15.3.
    (h35b : 2 * (c ^ 2 * n * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2 + Real.log 2) ≤ Real.log (M : ℝ)) :
    ENNReal.ofReal (2⁻¹ * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2) ≤ minimaxRiskDist (· ^ 2) g P := by
  sorry

end StatLean.Minimaxity
