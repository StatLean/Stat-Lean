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
`Finset.sup'` over a nonempty Finset.

FROZEN-FALSE corner (documented sorry). As literally stated over a general
`f : ι → ℝ` the equality is **false**: the outer `⨆ i, ⨆ (_ : i ∈ s), f i`
ranges over *all* of `ι`, and for `i ∉ s` the inner supremum is the junk value
`sSup (∅ : Set ℝ) = 0`. Hence `⨆ i ∈ s, f i = max (s.sup' hs f) 0` whenever
`ι \ s ≠ ∅`, so e.g. `⨆ i ∈ ({0} : Finset ℕ), (-1 : ℝ) = 0 ≠ -1 = sup'`.
The identity holds only when `s.sup' hs f ≥ 0` (in particular for the
nonnegative `|·|`-valued applications that consume it in the chaining files);
the general statement is frozen and cannot be closed without a nonnegativity
hypothesis. Kept as the file's structural sorry alongside
`expectation_max_finset_le` (which fails at `|s| = 1` for the same reason). -/
lemma biSup_finset_eq_sup' {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined and the real biSup
    -- is not junk; no book content
    (hs : s.Nonempty) (f : ι → ℝ)
    -- LEAN-ONLY: nonnegative family — REQUIRED (statement fix at the debt
    -- gate: for i ∉ s the inner sup is junk 0, so the unguarded identity is
    -- FALSE for negative values, e.g. ⨆ i ∈ {0}, (−1) = 0 ≠ −1; every
    -- chaining call site is |·|-valued so this is supplied uniformly as
    -- (fun i _ => abs_nonneg _))
    (h0 : ∀ i ∈ s, 0 ≤ f i) :
    (⨆ i ∈ s, f i) = s.sup' hs f := by
  sorry

set_option maxHeartbeats 1000000 in
/-- The pointwise supremum over a nonempty finite index set of integrable
functions is integrable (public Finset twin of the private domination helper
in `Maximal/FiniteMaximal.lean`). -/
lemma integrable_biSup_finset {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value; HDP §8.1
    (hs : s.Nonempty) {X : ι → Ω → ℝ}
    -- LEAN-ONLY: per-index integrability, dominates the finite sup; HDP §8.1
    (hint : ∀ i ∈ s, MeasureTheory.Integrable (X i) μ) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ s, X i ω) μ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  -- pointwise domination by the sum of absolute values
  have hbdd : ∀ ω, BddAbove (Set.range (fun i => ⨆ (_ : i ∈ s), X i ω)) := by
    intro ω
    refine ⟨∑ i ∈ s, |X i ω|, ?_⟩
    rintro y ⟨i, rfl⟩
    dsimp only
    by_cases hi : i ∈ s
    · rw [ciSup_pos hi]
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg (X i ω)) hi)
    · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hmeas : AEMeasurable (fun ω => ⨆ i ∈ s, X i ω) μ :=
    AEMeasurable.biSup (↑s) s.countable_toSet
      (fun i hi => (hint i (Finset.mem_coe.mp hi)).aemeasurable)
  refine MeasureTheory.Integrable.mono' (g := fun ω => ∑ i ∈ s, |X i ω|)
    (MeasureTheory.integrable_finset_sum s (fun i hi => (hint i hi).abs))
    hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- lower bound: `-∑ ≤ ⨆`
    have hi₀le : X i₀ ω ≤ ⨆ i ∈ s, X i ω :=
      le_ciSup_of_le (hbdd ω) i₀ (le_of_eq (ciSup_pos (f := fun _ => X i₀ ω) hi₀).symm)
    have : -(∑ i ∈ s, |X i ω|) ≤ X i₀ ω := by
      have h1 : -|X i₀ ω| ≤ X i₀ ω := neg_abs_le _
      have h2 : |X i₀ ω| ≤ ∑ i ∈ s, |X i ω| :=
        Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg (X i ω)) hi₀
      linarith
    linarith
  · -- upper bound: `⨆ ≤ ∑`
    refine Real.iSup_le (fun i => ?_) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    dsimp only
    by_cases hi : i ∈ s
    · rw [ciSup_pos hi]
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg (X i ω)) hi)
    · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
      rw [Real.iSup_of_isEmpty]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

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
      ≤ ENNReal.ofReal ((s.card : ℝ) * Real.exp (-t ^ 2 / (2 * σ2))) := by
  classical
  -- the max exceeds `t ≥ 0` only if some coordinate does (the biSup junk value
  -- `0` never exceeds `t ≥ 0`, so it drops out of the event)
  have hsub : {ω | t < ⨆ i ∈ s, X i ω} ⊆ ⋃ i ∈ s, {ω | t < X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have hle : (⨆ i ∈ s, X i ω) ≤ t := by
      refine Real.iSup_le (fun i => ?_) ht
      by_cases hi : i ∈ s
      · rw [ciSup_pos hi]; exact hcon i hi
      · haveI : IsEmpty (i ∈ s) := ⟨hi⟩
        rw [Real.iSup_of_isEmpty]; exact ht
    exact absurd hω (not_lt.mpr hle)
  calc μ {ω | t < ⨆ i ∈ s, X i ω}
      ≤ μ (⋃ i ∈ s, {ω | t < X i ω}) := measure_mono hsub
    _ ≤ ∑ i ∈ s, μ {ω | t < X i ω} := measure_biUnion_finset_le s _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h := (hX i hi).measure_sub_integral_lt_le ht
        simp only [hcenter i hi, sub_zero] at h
        exact h
    _ = ENNReal.ofReal ((s.card : ℝ) * Real.exp (-t ^ 2 / (2 * σ2))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **Finset maximal inequality — expectation bound** (Lu-BDA §6.2, Theorem
6.2 / HDP §2.5, Eq. (2.22)): Finset reindex of `expectation_max_le` via
`s.equivFin`; the per-level engine of HDP §8.1, Eq. (8.11).

FROZEN-FALSE corner (documented sorry). As stated the bound is **false** for
the same junk-`biSup` reason as `biSup_finset_eq_sup'`: over a general index
type `ι ⊋ s` the integrand `⨆ i ∈ s, X i ω` equals `(s.sup' _ (X · ω))⁺`, not
the honest max. At `|s| = 1` the RHS is `√σ² · √(2 log 1) = 0`, while the LHS
is `∫ (X_{i₀})⁺ ≥ 0`, strictly positive for any non-degenerate centered
sub-Gaussian `X_{i₀}` — a counterexample. The honest `Fin`-indexed
`expectation_max_le` (no junk, since `Fin d` is the whole index type) is the
correct engine; the Finset reindex needs `s.sup' _ (X · ω) ≥ 0` a.e. (true for
the `|·|`-valued chaining applications) which the frozen statement omits. -/
theorem expectation_max_finset_le {ι : Type*}
    -- USER-INPUT: probability-space context; Lu-BDA §6.2, Theorem 6.2
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness (reindex target `Fin s.card` must be nonempty)
    (hs : s.Nonempty) {σ2 : ℝ≥0} {X : ι → Ω → ℝ}
    -- USER-INPUT: E[X_i] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: X_i sub-Gaussian with variance proxy σ²; Lu-BDA §6.2
    (hX : ∀ i ∈ s, IsSubGaussian (X i) σ2 μ) :
    -- Statement fix at the debt gate: the conclusion is stated with
    -- `Finset.sup'` (junk-free), exactly mirroring the proven Fin-indexed
    -- `expectation_max_le`; the old biSup form was FALSE at |s| = 1.
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ
      ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log s.card) := by
  sorry

end StatLean.ConcentrationInequalities
