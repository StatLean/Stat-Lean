import StatLean.Minimaxity.LeCam.TwoPoint
import StatLean.Minimaxity.ForMathlib.LeCamInequality

/-!
# Example: uniform location family (Wainwright Example 15.5)

A non-regular parametric problem with a faster-than-`1/n` rate. For the uniform location family
`{Uniform[θ, θ+1] : θ ∈ ℝ}` and `n` i.i.d. samples, the Kullback–Leibler divergence is infinite for
distinct parameters, so Le Cam's two-point bound is applied via the **Hellinger** distance (Lemma
15.3) instead of Pinsker. The resulting minimax risk scales as `n⁻²`:
```
inf_θ̂ sup_θ 𝔼_θ[(θ̂ − θ)²] ≥ (1 − 1/√2)/128 · 1/n²        (Example 15.5).
```

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax rate for the uniform location family** (Wainwright Example 15.5): for the `n`-sample
model `P θ = Uniform[θ, θ+1]^{⊗n}`, the minimax risk for estimating `θ` under squared error is at
least `(1 − 1/√2)/128 · n⁻²` — the faster `n⁻²` rate of a non-regular problem.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.5. -/
theorem uniform_location_minimax_rate (n : ℕ) (hn : 1 ≤ n)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    -- USER-INPUT: `P θ` is the `n`-fold i.i.d. `Uniform[θ, θ+1]` product; Wainwright §15.2, Ex 15.5.
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc θ (θ + 1))) :
    ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 128 / (n : ℝ) ^ 2)
      ≤ minimaxRiskDist (· ^ 2) id P := by
  sorry

end StatLean.Minimaxity
