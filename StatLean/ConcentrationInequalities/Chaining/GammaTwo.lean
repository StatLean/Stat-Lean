import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Admissible sequences and the γ₂ functional

Talagrand's generic-chaining functional: an *admissible sequence* of a set
$T$ is an increasing-resolution sequence of subsets $(T_k)_{k \ge 0}$ with
$|T_0| = 1$ and $|T_k| \le 2^{2^k}$, and
$$ \gamma_2(T, d) \;=\; \inf_{(T_k)} \; \sup_{t \in T}
     \sum_{k=0}^{\infty} 2^{k/2}\, d(t, T_k), $$
the infimum over admissible sequences. Concept-layer file (no probability);
consumed by `Chaining/GenericChaining.lean`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.1, Definition 8.5.1, Eqs. (8.43) (admissible
sequence) and (8.45) (the γ₂ functional).

**Proof formalization notes.** `gammaFunctional` and `gammaTwo` are BOTH
`ℝ≥0∞`-valued (a real tsum/iSup would junk-degrade to `0` on divergent
sequences and corrupt the infimum downward); `2^{k/2}` is encoded as
`(Real.sqrt 2)^k`. The `nonempty` field of `AdmissibleSequence` is
Constitutive-by-necessity: Mathlib's `Metric.infDist x ∅ = 0` junk would
otherwise corrupt γ₂ downward. Edge behavior: `gammaTwo ∅ = ⊤` (infimum over
the empty type of admissible sequences — `card_zero` forces a point of `T`),
documented junk. Finiteness for finite `T` (`gammaTwo_lt_top_of_finite`) uses
the exhausting sequence `seq k = T` once `2^{2^k} ≥ |T|`. The book's "there
must be some `K` with `T_K = T`" step becomes the pseudometric-safe
`AdmissibleSequence.exists_eventually_dist_zero`: finite `T` + finite
functional ⇒ series terms → 0 ⇒ eventually a net point at distance `0`
(X-values are then a.e.-identified downstream). Named-sorry fallback of this
work item: `AdmissibleSequence.exists_eventually_dist_zero` (definitions,
finiteness, and the diameter lemmas proved).

**Bibliographic comments.** The γ₂ functional and generic chaining are due to
M. Talagrand, "Regularity of Gaussian processes," *Acta Math.* 159 (1987),
99–149, building on X. Fernique's majorizing measures (1975); the admissible-
sequence formulation is Talagrand, *The Generic Chaining*, Springer 2005, and
*Upper and Lower Bounds for Stochastic Processes*, Springer 2014, §2.3. See
the HDP §8.5 Notes.
-/

open Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- **Admissible sequence** (HDP §8.5.1, Definition 8.5.1, Eq. (8.43)): a
sequence of finite subsets of `T` with `|T₀| = 1` and `|T_k| ≤ 2^{2^k}`,
along which the γ₂ series is formed. -/
structure AdmissibleSequence (T : Set E) where
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): the level-`k` approximating
  finite subset `T_k`. -/
  seq : ℕ → Finset E
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): each level lies inside the
  carrier, `T_k ⊆ T`. -/
  subset_carrier : ∀ k, ↑(seq k) ⊆ T
  /-- Constitutive-by-necessity (HDP §8.5.1): each level is nonempty —
  Mathlib's `Metric.infDist x ∅ = 0` junk would corrupt γ₂ downward
  (the book's `|T₀| = 1` already forces nonemptiness at every level). -/
  nonempty : ∀ k, (seq k).Nonempty
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): the root level is a singleton,
  `|T₀| = 1`. -/
  card_zero : (seq 0).card = 1
  /-- Constitutive (HDP §8.5.1, Eq. (8.43)): the doubly-exponential
  cardinality budget `|T_k| ≤ 2^{2^k}`. -/
  card_le : ∀ k, (seq k).card ≤ 2 ^ 2 ^ k

/-- **γ₂ series along an admissible sequence** (HDP §8.5.1, Eq. (8.45), inner
quantity): `sup_{t ∈ T} Σ_k 2^{k/2} d(t, T_k)`, valued in `ℝ≥0∞` so that
divergent series register as `⊤` rather than junk `0`; `2^{k/2}` is encoded
as `(√2)^k`. -/
noncomputable def gammaFunctional {T : Set E} (A : AdmissibleSequence T) : ℝ≥0∞ :=
  ⨆ t ∈ T, ∑' k : ℕ, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))

/-- **The γ₂ functional** (HDP §8.5.1, Eq. (8.45)): the infimum of the γ₂
series over all admissible sequences, in `ℝ≥0∞`. Edge behavior: `⊤` for
`T = ∅` (no admissible sequence exists), documented junk. -/
noncomputable def gammaTwo (T : Set E) : ℝ≥0∞ :=
  ⨅ A : AdmissibleSequence T, gammaFunctional A

/-- Nonempty sets admit admissible sequences (the constant singleton
sequence). -/
lemma nonempty_admissibleSequence {T : Set E}
    -- LEAN-ONLY: nonemptiness supplies the singleton root; HDP §8.5.1
    (hne : T.Nonempty) :
    Nonempty (AdmissibleSequence T) := by sorry

/-- γ₂ is bounded by the series of any admissible sequence (`iInf_le`). -/
lemma gammaTwo_le {T : Set E} (A : AdmissibleSequence T) :
    -- LEAN-ONLY: iInf_le; no book content
    gammaTwo T ≤ gammaFunctional A := by sorry

/-- Finiteness of γ₂ for finite `T` (HDP §8.5.2, proof Step 1, "T finite
makes γ₂ finite"): the exhausting sequence `seq k = T` once `2^{2^k} ≥ |T|`
makes the series a finite sum. -/
lemma gammaTwo_lt_top_of_finite {T : Set E}
    -- LEAN-ONLY: T finite (the exhausting sequence exists)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness (γ₂ ∅ = ⊤ junk)
    (hne : T.Nonempty) :
    gammaTwo T < ⊤ := by sorry

/-- Pseudometric-safe chain end (HDP §8.5.2, proof Step 1, the "some `K` has
`T_K = T`" step): finite `T` + finite functional force the series terms to
`0`, so eventually every point of `T` has a net point at distance `0`. -/
lemma AdmissibleSequence.exists_eventually_dist_zero {T : Set E}
    -- LEAN-ONLY: T finite (finitely many values, series terms → 0)
    (hfin : T.Finite) {A : AdmissibleSequence T}
    -- LEAN-ONLY: finite functional (otherwise the series carries no
    -- information); HDP §8.5.2 Step 1
    (hA : gammaFunctional A ≠ ⊤) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ t ∈ T, ∃ a ∈ A.seq k, dist t a = 0 := by sorry

/-- The `k = 0` term of the γ₂ series (HDP §8.5.2): the distance to the root
singleton is dominated by the functional. -/
lemma ofReal_infDist_zero_le_gammaFunctional {T : Set E}
    (A : AdmissibleSequence T) {t : E}
    -- LEAN-ONLY: membership so the biSup dominates the t-series
    (ht : t ∈ T) :
    ENNReal.ofReal (Metric.infDist t ↑(A.seq 0)) ≤ gammaFunctional A := by sorry

/-- Diameter domination (HDP §8.5.2, proof Step 3): `seq 0` is a singleton
`{a₀}` and `diam T ≤ 2 sup_t d(t, a₀)`; absorbs the `u·diam` term of the
tail event into `u·γ₂`. -/
lemma ofReal_diam_le_two_mul_gammaFunctional {T : Set E}
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: boundedness so `Metric.diam` is meaningful
    (hbd : Bornology.IsBounded T)
    (A : AdmissibleSequence T) :
    ENNReal.ofReal (Metric.diam T) ≤ 2 * gammaFunctional A := by sorry

end StatLean.ConcentrationInequalities
