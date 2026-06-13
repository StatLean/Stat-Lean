import StatLean.ConcentrationInequalities.Bernstein.Defs
import StatLean.ConcentrationInequalities.SubExponential.Defs

/-!
# Bernstein condition ⇒ sub-exponential MGF bound  (Lu-BDA §4.1, Step 1)

A random variable satisfying the Bernstein moment condition is sub-exponential:
`HasBernsteinCondition X σ2 b μ → IsSubExponential X (2 * (NNReal.sqrt σ2 ⊔ b)) μ`.

## Constant deviation from the stated task
The original task asks for `α = 2 * (σ2 ⊔ b)`, where `σ2 = Var(X)` is the **variance**
and `b` is the Bernstein tail scale.  This formula mixes units: `σ2` is quadratic while
`b` is linear.  The formula fails when `σ2 > 2 * (σ2 ⊔ b)^2`; for example, with
`σ2 = 0.01` and the minimal admissible `b = 1/30`, we get `2*(σ2⊔b)^2 ≈ 0.0022 < 0.01`.

The provable parameter is **`α = 2 * (NNReal.sqrt σ2 ⊔ b)`**, which uses the standard
deviation `NNReal.sqrt σ2` (Lu-BDA §4.1 implicitly works with the standard deviation in the
geometric-series range condition).  With `s := NNReal.sqrt σ2 ⊔ b`:
* **Range** — `|λ| ≤ 1/α = 1/(2s)` implies `|λ| ≤ 1/(2b)` (since `s ≥ b`), so
  `|λ|·b ≤ 1/2` and the Bernstein geometric series converges.
* **Variance bound** — `σ2 = (NNReal.sqrt σ2)^2 ≤ s^2 ≤ 2s^2 = α^2/2`, so
  `exp(λ²·σ2) ≤ exp(λ²·α^2/2)`.

## One named sorry
`bernstein_key` below covers both the integrability of `exp(l·X)` and the MGF power-series
bound.  The math is clear (MCT + geometric series + `hasFPowerSeriesAt_mgf`); the gap is
bridging `MeasureTheory.lintegral_tsum` to the formal power series framework, in particular
showing that the radius of `hasFPowerSeriesAt_mgf` at 0 is ≥ `1/b` (which requires
connecting the convergence of the moment series to the `p.radius` field of
`HasFPowerSeriesAt`).  Lemmas reached for: `hasFPowerSeriesAt_mgf`,
`iteratedDeriv_mgf_zero`, `HasFPowerSeriesOnBall.hasSum`,
`MeasureTheory.lintegral_tsum`, `Real.hasSum_pow_div_factorial`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {X : Ω → ℝ} {σ2 b : ℝ≥0} {μ : Measure Ω}

/-! ### The one named sorry -/

/-- **[LEAN-ONLY sorry]**  For `|l| ≤ 1 / α` with `α = 2 * (√σ2 ⊔ b)`, the exponential
`ω ↦ exp(l · X ω)` is integrable and the MGF satisfies the sub-exponential bound.

**Proof sketch**:

1. *Integrability via MCT.* The Bernstein bounds give
   `E[|X|^k] ≤ (σ2/2)·k!·b^{k-2}` for k ≥ 3, plus `E[X^2] = σ2`, and
   `E[|X|] ≤ sqrt(σ2)` (Cauchy–Schwarz under IsProbabilityMeasure).
   For `|l|b < 1` (which holds since `|l| ≤ 1/(2s)` and `s ≥ b`):
   ```
   ∑_k |l|^k/k! · E[|X|^k] ≤ 1 + |l|·√σ2 + l²σ2/2
                              + (σ2/2)·l²·(|l|b)/(1-|l|b) < ∞
   ```
   By `MeasureTheory.lintegral_tsum` (Tonelli) on the pointwise series
   `exp(|l||X|) = ∑_k (|l||X|)^k/k!`, the lintegral is finite, giving integrability.

2. *MGF series.* From integrability, `0 ∈ interior(integrableExpSet X μ)`.
   `hasFPowerSeriesAt_mgf` then gives `mgf X μ l = ∑_n l^n/n! · E[X^n]`.

3. *Bound.* Split at n = 2:
   - n=0: 1 (probability measure); n=1: 0 (mean_zero); n=2: l²σ2/2.
   - n≥3 tail: `≤ (σ2/2)·l²·|l|b/(1-|l|b) ≤ l²σ2/2` (since `|l|b ≤ 1/2`).
   So `mgf X μ l ≤ 1 + l²σ2 ≤ exp(l²σ2) ≤ exp(l²·α²/2)` (since `σ2 ≤ 2s² = α²/4·2`).

**Mathlib gap** — The key missing bridge: showing that the formal power series obtained from
`hasFPowerSeriesAt_mgf` at 0 has radius `p.radius ≥ ENNReal.ofReal (1/↑b)`, so that
`HasFPowerSeriesOnBall.hasSum` applies at `l`.  This requires connecting the
`MeasureTheory.lintegral_tsum` convergence (in ENNReal) to the
`FormalMultilinearSeries.radius` definition, through NNReal ↔ ENNReal coercions and
factorial arithmetic.  The mathematical content is straightforward; the Lean infrastructure
gap is real. -/
private lemma bernstein_key [IsProbabilityMeasure μ]
    (hB : HasBernsteinCondition X σ2 b μ)
    {l : ℝ}
    (hl : |l| ≤ 1 / ((2 * (NNReal.sqrt σ2 ⊔ b) : ℝ≥0) : ℝ)) :
    Integrable (fun ω => Real.exp (l * X ω)) μ ∧
    mgf X μ l ≤ Real.exp (l ^ 2 * ((2 * (NNReal.sqrt σ2 ⊔ b) : ℝ≥0) : ℝ) ^ 2 / 2) := by
  sorry

/-! ### Main theorem -/

/-- A random variable satisfying the Bernstein condition (Lu-BDA §4.1) is sub-exponential
with parameter `α = 2 · (√σ2 ⊔ b)`.

**Proof**: from `bernstein_key` (one named sorry) plus the mean-zero centering.
For `|l| ≤ 1/α`:
- `mgf_le`: since `E[X] = 0`, the centered MGF equals the uncentered one; apply the sorry.
- `integrable_exp_mul`: same centering, integrability from the sorry.

**Constant deviation from the task statement** — the task asks for `α = 2*(σ2⊔b)`.
See the module header for why this is incorrect and `α = 2*(NNReal.sqrt σ2 ⊔ b)` is the
provable form.

-- USER-INPUT: `X` (random variable), `σ2`, `b` (Bernstein parameters); Lu-BDA §4.1.
-- LEAN-ONLY: `[IsProbabilityMeasure μ]`; Lu-BDA §4.1 works on a probability space
   (tacit from the book context). -/
theorem isSubExponential_of_hasBernsteinCondition
    [IsProbabilityMeasure μ]
    -- USER-INPUT: Bernstein condition for X; Lu-BDA §4.1.
    (hB : HasBernsteinCondition X σ2 b μ) :
    IsSubExponential X (2 * (NNReal.sqrt σ2 ⊔ b)) μ where
  mgf_le l hl := by
    -- X ω - E[X] = X ω - 0 = X ω  (by mean_zero)
    have hcenter : (fun ω => X ω - ∫ x, X x ∂μ) = X := by
      funext ω; simp [hB.mean_zero]
    rw [hcenter]
    exact (bernstein_key hB hl).2
  integrable_exp_mul l hl := by
    -- exp(l · (X ω - E[X])) = exp(l · X ω)  (by mean_zero)
    simp_rw [hB.mean_zero, sub_zero]
    exact (bernstein_key hB hl).1

end StatLean.ConcentrationInequalities
