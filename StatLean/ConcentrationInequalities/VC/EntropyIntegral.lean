import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Dudley entropy integral for VC classes

The entropy-integral evaluation used in Theorem 8.3.15's proof: with the
sample-independent covering bound
$N(T', \varepsilon) \le (4/\varepsilon)^{22 d}$ on $(0, 2)$,
$$ \int_0^2 \sqrt{22\, d \, \log\bigl(4/\varepsilon\bigr)}\;d\varepsilon
   \;\le\; 27 \sqrt{d}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6 — the "bounded entropy integral" step in
the proof of Theorem 8.3.15 (the book leaves the integral as an unnamed
absolute constant).

**Proof formalization notes.** VC owns its own entropy integral (batch
decision R7): this file is self-contained interval-integral analysis with no
stub dependencies, and `VC/LawOfLargeNumbers.lean` plugs it into the
chaining cluster's `dudley_inequality_abs` directly. The `22` (not the
covering theorem's `21`) absorbs the factor-2 covering loss from the
symmetrized index set `T' = empProj '' F ∪ (−(empProj '' F))`, and the
`4/ε` (not `2/ε`) extends the bound to the full diameter range
`ε ∈ (0, 2)`. Evaluation is by the crude comparison `log y ≤ y − 1 ≤ y`
(`Real.log_le_sub_one_of_pos`), giving
`√(log(4/ε)) ≤ 2/√ε`, and `∫₀² ε^{−1/2} dε = 2√2`; the frozen numeral is
`27` from `√22 · 2 · 2√2 = 8√44 ≈ 26.53 ≤ 27`. Integrability of the
integrand near `0` is by domination by `ε^{−1/2}` (integrable rpow,
exponent `> −1`). Edge behavior: the integrand is junk (`log` of a
nonpositive argument) outside `(0, 4)`, but the interval of integration is
`(0, 2)`. Named-sorry fallback of this work item: `entropyIntegral_le`
(keep the two helper lemmas real; sorry only the final interval-integral
assembly).

**Bibliographic comments.** The entropy integral is R. M. Dudley's ("The
sizes of compact subsets of Hilbert space and continuity of Gaussian
processes," *J. Funct. Anal.* 1 (1967), 290–330); its finiteness for VC
classes — the fact that `∫₀² √(d·log(4/ε)) dε ≍ √d` — is the engine of the
uniform CLT/LLN for VC classes, HDP §8.3 Notes.
-/

open MeasureTheory intervalIntegral

namespace StatLean.ConcentrationInequalities

/-- Crude entropy-integrand comparison `√(log(4/ε)) ≤ 2/√ε` on `(0, 2]`
(LEAN-ONLY: `log y ≤ y` via `Real.log_le_sub_one_of_pos`; no book
content). -/
lemma sqrt_log_le_two_div_sqrt {ε : ℝ}
    -- LEAN-ONLY: the comparison's domain; matches the integration interval.
    (hε : 0 < ε) (hε2 : ε ≤ 2) :
    Real.sqrt (Real.log (4 / ε)) ≤ 2 / Real.sqrt ε := by
  sorry

/-- Interval integrability of the VC entropy integrand on `(0, 2)`
(LEAN-ONLY: domination by `ε^{−1/2}`, integrable rpow with exponent
`> −1`). -/
lemma intervalIntegrable_sqrt_log_mul {c : ℝ}
    -- LEAN-ONLY: nonnegative multiplier so `√(c·log)` factors through `√c`.
    (hc : 0 ≤ c) :
    IntervalIntegrable (fun ε => Real.sqrt (c * Real.log (4 / ε)))
      MeasureTheory.volume 0 2 := by
  sorry

/-- **Entropy integral bound for VC classes** (HDP §8.3.6, Theorem 8.3.15
proof step): `∫₀² √(22·d·log(4/ε)) dε ≤ 27·√d`. Frozen numeral `27` from
`√22 · 2 · 2√2 = 8√44 ≈ 26.53`. -/
theorem entropyIntegral_le {d : ℕ}
    -- USER-INPUT: 1 ≤ d (nondegenerate VC dimension); HDP §8.3.6.
    (hd1 : 1 ≤ d) :
    ∫ ε in (0 : ℝ)..2, Real.sqrt (22 * d * Real.log (4 / ε))
      ≤ 27 * Real.sqrt d := by
  sorry

end StatLean.ConcentrationInequalities
