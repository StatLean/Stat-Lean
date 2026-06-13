import Mathlib.Probability.Moments.SubGaussian

/-!
# Bernstein condition — definition

Book definition (Lu, *Big Data Analysis* §4.1, "Bernstein Condition"): a random
variable `X` with `E X = 0` and `Var(X) = σ²` satisfies the *Bernstein
condition with parameter `b`* if

`E |X|ᵏ ≤ (σ²/2) · k! · bᵏ⁻²` for all `k ≥ 3`.

The `k = 1, 2` cases are omitted because they are forced by `E X = 0` and
`Var(X) = σ²` (the `k = 2` case is the variance itself). Bounded variables
satisfy it (Lu §4.1, Example: `|X| ≤ B` ⇒ parameter `B/3`); the headline use is
"Bernstein condition ⇒ sub-exponential ⇒ Bernstein inequality" (`Bernstein/MGFBound.lean`,
`Bernstein/Bernstein.lean`).

This is a concept-layer foundation; it is theorem-agnostic.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `HasBernsteinCondition X σ2 b μ`: the centered random variable `X` (with
`E X = 0` and `Var X = σ2` under `μ`) satisfies the Bernstein moment bound with
parameter `b`, i.e. `E |X|ᵏ ≤ (σ2/2)·k!·bᵏ⁻²` for every `k ≥ 3`
(Lu-BDA §4.1, "Bernstein Condition"). -/
structure HasBernsteinCondition (X : Ω → ℝ) (σ2 b : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  /-- Constitutive (Lu-BDA §4.1): the book states the condition for a centered
  variable, `E X = 0`. -/
  mean_zero : ∫ ω, X ω ∂μ = 0
  /-- Constitutive (Lu-BDA §4.1): the parameter `σ2` is the variance of `X`;
  with `E X = 0` this is `E[X²] = σ2`. -/
  variance_eq : ∫ ω, (X ω) ^ 2 ∂μ = (σ2 : ℝ)
  /-- Constitutive (Lu-BDA §4.1): the defining moment bound
  `E |X|ᵏ ≤ (σ2/2)·k!·bᵏ⁻²` for all `k ≥ 3`. Removing it makes the object not
  the book's Bernstein-condition variable. (`k - 2` is `ℕ`-subtraction; harmless
  since `k ≥ 3`.) -/
  moment_le : ∀ k : ℕ, 3 ≤ k →
    ∫ ω, |X ω| ^ k ∂μ ≤ (σ2 : ℝ) / 2 * (k.factorial : ℝ) * (b : ℝ) ^ (k - 2)

end StatLean.ConcentrationInequalities
