import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Varshamov–Gilbert packing of the binary hypercube (Wainwright Example 5.3)

A Chapter-5 metric-entropy prerequisite for the local-packing minimax lower bounds: there is a
subset of the hypercube `{0,1}^m` that is `1/4`-separated in the rescaled Hamming metric and has
exponentially large cardinality,
```
log M_H(1/4; {0,1}^m) ≥ m/10                          (Example 5.3, Eq. (5.3))
```
i.e. a set `T` with `log |T| ≥ m/10` and pairwise Hamming distance `≥ m/4`. This is the
Gilbert–Varshamov bound. It underlies the local packings used in Examples 15.11 and 15.15.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.3, Eq. (5.3)
(used in Chapter 15, §15.2.2 / §15.3.3, Examples 15.11 and 15.15).
-/

open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Gilbert–Varshamov bound** (Wainwright Example 5.3, Eq. (5.3)): for every `m`, the binary
hypercube `{0,1}^m` contains a `1/4`-separated set (in the rescaled Hamming metric) of cardinality
at least `e^{m/10}` — equivalently a set `T` with `log |T| ≥ m/10` whose elements are pairwise at
Hamming distance `≥ m/4`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.3, Eq. (5.3). -/
theorem exists_hamming_packing (m : ℕ) :
    ∃ T : Finset (Fin m → Bool),
      (m / 10 : ℝ) ≤ Real.log T.card ∧
      ∀ α ∈ T, ∀ β ∈ T, α ≠ β → (m / 4 : ℝ) ≤ (hammingDist α β : ℝ) := by
  sorry

end StatLean.Minimaxity
