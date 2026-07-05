import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal

/-!
# Finset-indexed maximal inequalities for sub-Gaussian variables

Finset-indexed adapters of the existing `Fin d`-indexed maximal inequalities
(`Maximal/FiniteMaximal.lean`): for a nonempty finite index set
$s$ and centered sub-Gaussian variables $(X_i)_{i \in s}$ with variance
proxy $\sigma^2$,
$$ \mathbb{P}\Bigl(\max_{i \in s} X_i > t\Bigr)
     \le |s|\, e^{-t^2/(2\sigma^2)}, \qquad
   \mathbb{E}\Bigl[\max_{i \in s} X_i\Bigr] \le \sigma \sqrt{2 \log |s|}, $$
so that chaining levels can take maxima over pair-Finsets (`closePairs`)
directly, without re-indexing to `Fin d` at every level.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.5, Eq. (2.22) / Exercise 2.5.10; the underlying
`Fin d` theorems are Lu, *Big Data Analysis*, §6.2, Theorem 6.2 (Finite
Maximal Inequality). Used at each chaining level in HDP §8.1, Eq. (8.11).

**Proof formalization notes.** Pure reindexing via `s.equivFin` of
`tail_max_le` and `expectation_max_le` (`Maximal/FiniteMaximal.lean`) — no
new probabilistic content. The finite maximum is written as the set-bounded
supremum `⨆ i ∈ s, X i ω`; `biSup_finset_eq_sup'` is the conversion helper
between this `biSup` form and `Finset.sup'` (needed because Mathlib's Finset
API and the chaining assembly use different maxima carriers).
`integrable_biSup_finset` is the public Finset twin of `FiniteMaximal`'s
private domination helper. Named-sorry fallback of this work item:
`tail_max_finset_le` (the expectation form `expectation_max_finset_le` is the
one `DiscreteDudley` needs and lands first).

**Bibliographic comments.** The maximal inequality for finitely many
sub-Gaussian variables is folklore via the Cramér–Chernoff method; standard
modern references are Boucheron–Lugosi–Massart, *Concentration Inequalities*,
Oxford 2013, §2.5, and HDP §2.5. No single seminal attribution is
appropriate; see the HDP Chapter 2 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conversion between the set-bounded supremum `⨆ i ∈ s, f i` and
`Finset.sup'` over a nonempty Finset (both equal the honest finite maximum). -/
lemma biSup_finset_eq_sup' {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined and the real biSup
    -- is not junk; no book content
    (hs : s.Nonempty) (f : ι → ℝ) :
    (⨆ i ∈ s, f i) = s.sup' hs f := by sorry

/-- The pointwise supremum over a nonempty finite index set of integrable
functions is integrable (public Finset twin of the private domination helper
in `Maximal/FiniteMaximal.lean`). -/
lemma integrable_biSup_finset {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value; HDP §8.1
    (hs : s.Nonempty) {X : ι → Ω → ℝ}
    -- LEAN-ONLY: per-index integrability, dominates the finite sup; HDP §8.1
    (hint : ∀ i ∈ s, MeasureTheory.Integrable (X i) μ) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ s, X i ω) μ := by sorry

/-- **Finset maximal inequality — tail bound** (Lu-BDA §6.2, Theorem 6.2 /
HDP §2.5, Eq. (2.22)): Finset reindex of `tail_max_le` via `s.equivFin`. -/
theorem tail_max_finset_le {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness (reindex target `Fin s.card` must be nonempty)
    (hs : s.Nonempty) {σ2 : ℝ≥0} {X : ι → Ω → ℝ}
    -- USER-INPUT: E[X_i] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: X_i sub-Gaussian with variance proxy σ²; Lu-BDA §6.2
    (hX : ∀ i ∈ s, IsSubGaussian (X i) σ2 μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0, ours strictly stronger); Lu-BDA §6.2
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < ⨆ i ∈ s, X i ω}
      ≤ ENNReal.ofReal ((s.card : ℝ) * Real.exp (-t ^ 2 / (2 * σ2))) := by sorry

/-- **Finset maximal inequality — expectation bound** (Lu-BDA §6.2, Theorem
6.2 / HDP §2.5, Eq. (2.22)): Finset reindex of `expectation_max_le` via
`s.equivFin`; the per-level engine of HDP §8.1, Eq. (8.11). -/
theorem expectation_max_finset_le {ι : Type*}
    -- USER-INPUT: probability-space context; Lu-BDA §6.2, Theorem 6.2
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness (reindex target `Fin s.card` must be nonempty)
    (hs : s.Nonempty) {σ2 : ℝ≥0} {X : ι → Ω → ℝ}
    -- USER-INPUT: E[X_i] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: X_i sub-Gaussian with variance proxy σ²; Lu-BDA §6.2
    (hX : ∀ i ∈ s, IsSubGaussian (X i) σ2 μ) :
    ∫ ω, ⨆ i ∈ s, X i ω ∂μ
      ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log s.card) := by sorry

end StatLean.ConcentrationInequalities
