import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The entropy integrand √log 𝒩(T, d, ε)

The integrand of Dudley's entropy integral,
$$ \varepsilon \longmapsto \sqrt{\log \mathcal{N}(T, d, \varepsilon)}, $$
as a total real-valued function `sqrtLogCov`, with its monotonicity,
vanishing beyond the diameter, boundedness by $\sqrt{\log |T|}$,
unconditional measurability, and integrability on $(0, D]$. Concept-layer
file, consumed by `Chaining/EntropySum.lean` and all chaining assembly files.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.3 (the integrand of the Dudley
entropy integral) and Remark 8.1.7.

**Proof formalization notes.** `sqrtLogCov T ε :=
√(log ((coveringNumber T ε).toNat))` is total, with **junk value `0` when
`coveringNumber T ε = ⊤`** (`ENat.toNat ⊤ = 0`, `log 0 = 0` junk composing to
`0`). The junk zone is never load-bearing: every theorem consuming it carries
`T.Finite` or an explicit `≠ ⊤` hypothesis — an upper-bound RHS evaluated in
the junk zone would be spuriously SMALL, hence unsound to state without those
hypotheses (they are USER-INPUT "T totally bounded", HDP p.227 footnote, not
laundering). Measurability is UNCONDITIONAL: `ε ↦ coveringNumber T ε` is a
globally antitone `ℕ∞`-valued function (`Antitone.measurable`), `toNat` is
measurable on the countable discrete `ℕ∞`, and cast/log/sqrt are continuous —
so no measurability hypotheses pollute the integral statements. Named-sorry
fallback of the entropy work item lives in `Chaining/EntropySum.lean`
(`sum_window_le_two_mul_dudleyIntegral`); this file's lemmas are all
elementary.

**Bibliographic comments.** The metric entropy $\log \mathcal{N}$ is due to
A. N. Kolmogorov and V. M. Tikhomirov, "ε-entropy and ε-capacity of sets in
function spaces," *Uspekhi Mat. Nauk* 14 (1959), 3–86; its square-root
integral as a modulus for Gaussian processes is R. M. Dudley, *J. Funct.
Anal.* 1 (1967), 290–330. See the HDP Chapter 8 Notes.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- **Entropy integrand** (HDP §8.1, Theorem 8.1.3): the function
`ε ↦ √(log 𝒩(T, d, ε))`, total and real-valued. Edge behavior: junk value
`0` when `coveringNumber T ε = ⊤` (`toNat ⊤ = 0`, then `log 0 = 0` junk);
also `0` whenever `𝒩 ≤ 1` (in particular for `ε ≥ diam T`). The junk zone is
never load-bearing — consumers carry `T.Finite` or `≠ ⊤`. -/
noncomputable def sqrtLogCov (T : Set E) (ε : ℝ) : ℝ :=
  Real.sqrt (Real.log ((coveringNumber T ε).toNat : ℝ))

lemma sqrtLogCov_nonneg (T : Set E) (ε : ℝ) :
    -- LEAN-ONLY: √ is nonneg by convention; no book content
    0 ≤ sqrtLogCov T ε := by sorry

/-- The integrand vanishes beyond the diameter (HDP §8.1, Remark 8.1.7:
`𝒩 = 1` at `ε ≥ diam T`). -/
lemma sqrtLogCov_eq_zero_of_diam_le {T : Set E}
    -- LEAN-ONLY: nonemptiness (empty T has 𝒩 = 0, a different corner)
    (hne : T.Nonempty)
    -- LEAN-ONLY: boundedness so `Metric.diam` is meaningful
    (hbd : Bornology.IsBounded T)
    -- LEAN-ONLY: nonnegative radius
    {ε : ℝ} (hε : 0 ≤ ε)
    -- LEAN-ONLY: radius above the diameter; HDP §8.1 Remark 8.1.7
    (h : Metric.diam T ≤ ε) :
    sqrtLogCov T ε = 0 := by sorry

/-- Antitonicity of the integrand (HDP §8.1, p. 226 monotonicity step):
`coveringNumber` is antitone and `toNat` is monotone below `⊤`. -/
lemma sqrtLogCov_anti {T : Set E} {ε δ : ℝ}
    -- LEAN-ONLY: radius comparison
    (h : ε ≤ δ)
    -- USER-INPUT: finite covering number at the smaller radius (T totally
    -- bounded); HDP p.227 footnote — guards the toNat junk zone
    (hfin : coveringNumber T ε ≠ ⊤) :
    sqrtLogCov T δ ≤ sqrtLogCov T ε := by sorry

/-- Stabilization at small radii (HDP §8.1, proof Step 1): `𝒩 ≤ |T|` always,
so the integrand is bounded by `√(log |T|)`. -/
lemma sqrtLogCov_le_sqrt_log_ncard {T : Set E}
    -- LEAN-ONLY: T finite so `T.ncard` is the honest cardinality
    (hfin : T.Finite) (ε : ℝ) :
    sqrtLogCov T ε ≤ Real.sqrt (Real.log T.ncard) := by sorry

/-- Unconditional measurability of the entropy integrand: the antitone
`ℕ∞`-valued core is measurable (`Antitone.measurable`), `toNat` is measurable
on the countable discrete `ℕ∞`, and cast/log/sqrt are continuous. -/
lemma measurable_sqrtLogCov (T : Set E) :
    Measurable (sqrtLogCov T) := by sorry

/-- Integrability on `(0, D]` (HDP §8.1): bounded by `√(log |T|)` on a set of
finite measure. -/
lemma integrableOn_sqrtLogCov_Ioc {T : Set E}
    -- LEAN-ONLY: T finite gives the uniform bound √(log |T|)
    (hfin : T.Finite) {D : ℝ} :
    MeasureTheory.IntegrableOn (sqrtLogCov T) (Set.Ioc 0 D)
      MeasureTheory.volume := by sorry

/-- Consumer plug-in monotonicity (HDP §8.2/§8.3 applications): a pointwise
covering-number bound `𝒩 ≤ b` transfers to the integrand. -/
lemma sqrtLogCov_le_sqrt_log_of_le {T : Set E}
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {ε : ℝ} {b : ℝ}
    -- USER-INPUT: finite covering number (T totally bounded); HDP p.227
    (h⊤ : coveringNumber T ε ≠ ⊤)
    -- USER-INPUT: the entropy bound 𝒩(T,d,ε) ≤ b; HDP §8.2/§8.3 applications
    (hb : ((coveringNumber T ε).toNat : ℝ) ≤ b)
    -- LEAN-ONLY: b ≥ 1 so `log b ≥ 0` and √ is monotone on the range
    (hb1 : 1 ≤ b) :
    sqrtLogCov T ε ≤ Real.sqrt (Real.log b) := by sorry

end StatLean.ConcentrationInequalities
