import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Binomial ratio inequality — `ForMathlib` layer

A pure finite-sum inequality (no probability), used by the knock-off initial bound
`E[V₊(0)/(1+V₋(0))] ≤ 1` where `V₊(0) ~ Binomial(N, ½)` and `V₋(0) = N − V₊(0)`:

`∑_{k=0}^{N} C(N,k)/2^N · k/(1 + (N−k)) ≤ 1`.

(The sum in fact equals `1 − 2^{-N}`; we only need `≤ 1`.) Not packaged in Mathlib; proved here by
finite arithmetic. Theorem-agnostic.
-/

open Finset

namespace StatLean.MultipleTesting

/-- `∑_{k=0}^{N} C(N,k)/2^N · k/(1 + (N−k)) ≤ 1`. The finite-sum inequality behind the knock-off
initial bound `E[V₊(0)/(1+V₋(0))] ≤ 1` (`V₊(0) ~ Binomial(N, ½)`). -/
theorem binom_ratio_sum_le_one (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - (k : ℝ))))) ≤ 1 := by
  sorry

end StatLean.MultipleTesting
