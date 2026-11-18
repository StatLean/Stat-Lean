/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The real-valued Poisson mass function

`poissonPMFReal r n = exp (-r) * r ^ n / n!` for a rate `r : ℝ≥0`, including `r = 0`. Mathlib
represents the Poisson law as the measure `poissonMeasure r`; StatLean's conjugate-prior and
empirical-Bayes models use the real-valued mass function. `hasSum_one_poissonMeasure` states that
it sums to `1`.
-/

noncomputable section

namespace ProbabilityTheory

open Real
open scoped NNReal Nat

/-- The real-valued Poisson mass function `exp (-r) * r ^ n / n!`, for every rate `r : ℝ≥0`. -/
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / (n)!

alias poissonPMFRealSum := hasSum_one_poissonMeasure

lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

end ProbabilityTheory
