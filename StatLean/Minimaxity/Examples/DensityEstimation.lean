import StatLean.Minimaxity.Fano.LocalPacking
import StatLean.Minimaxity.Fano.YangBarron
import StatLean.Minimaxity.ForMathlib.Packing.HammingPacking

/-!
# Example: minimax risk for density estimation (Wainwright Examples 15.15, 15.22)

Estimating an entire twice-smooth density `f ∈ ℱ₂` in the squared Hellinger metric, from `n` i.i.d.
samples, has minimax risk
```
sup_{f ∈ ℱ₂} H²(f̂ ‖ f) ≳ n^{-4/5}                          (Examples 15.15, 15.22),
```
proved two ways: by Fano's local-packing method over a Hamming-separated subfamily of perturbed
densities (Example 15.15), and more directly by the Yang–Barron method using the `L²` metric entropy
of `ℱ₂` (Example 15.22).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3, Examples 15.15, 15.22.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for density estimation in Hellinger distance** (Wainwright Examples 15.15/15.22):
for the twice-smooth density class `ℱ₂` and `n` i.i.d. samples, the minimax risk in squared
Hellinger distance is at least `c · n^{-4/5}`.

The functional `g i` records the density `f i` (decisions are densities; the loss is the squared
Hellinger distance, encoded as `edist` on the density class).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3, Examples 15.15, 15.22. -/
theorem density_estimation_hellinger_rate {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    [PseudoEMetricSpace Ω] (n : ℕ) (hn : 1 ≤ n)
    (g : ι → Ω) (Pn : Kernel ι (Fin n → ℝ)) [IsMarkovKernel Pn]
    -- USER-INPUT: `g i` is the density `f i` of the twice-smooth class `ℱ₂`, with the squared
    -- Hellinger loss encoded as `edist`; Wainwright §15.3, Examples 15.15/15.22.
    (hclass : ∀ i, True)
    -- USER-INPUT: `Pn i` is the `n`-fold i.i.d. product of `f i`; Wainwright §15.3.
    (hPn : ∀ i, IsMarkovKernel Pn) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * (n : ℝ) ^ (-(4 : ℝ) / 5)) ≤ minimaxRiskDist id g Pn := by
  sorry

end StatLean.Minimaxity
