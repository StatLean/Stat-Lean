import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal

/-!
# Countable-supremum lift engines

Index-polymorphic monotone-convergence engines turning **per-finite-subset**
bounds into **countable-supremum** bounds, in the junk-free carriers:

* `lintegral_biSup_le_of_forall_finset` — if
  `∫⁻ ⨆_{i∈F} g_i ≤ B` for every finite `F ⊆ C`, then
  `∫⁻ ⨆_{i∈C} g_i ≤ B` for countable `C` (`g` valued in `ℝ≥0∞`);
* `measure_exists_lt_le_of_forall_finset` (and its pair variant) — a uniform
  per-finite-window tail bound `μ{thr < max_F f} ≤ β` passes to the event
  that SOME member (pair) of the countable family exceeds the threshold;
* Bochner bridges `integrable_biSup_of_lintegral_biSup_ne_top` /
  `integral_biSup_le_of_lintegral_biSup_le` recovering real-integral displays
  from the `ℝ≥0∞` primaries under a `≠ ⊤` guard;
* pointwise plumbing: `lintegral_biSup_finset_ofReal_eq` (finite
  `⨆ ENNReal.ofReal` ↔ `ENNReal.ofReal ∘ ∫ Finset.sup'`),
  `toReal_biSup_ofReal` (the one infinite `ofReal`/`⨆` commutation, guarded),
  and the threshold bridges `exists_lt_of_lt_biSup_real` /
  `exists_pair_lt_of_lt_biSup_real` absorbing the `Real.sSup` junk value.

These generalize the two lifts previously inlined in
`dudley_inequality_countable` (`Chaining/Dudley.lean`) and
`dudley_tail_three_term_countable` (`Chaining/DudleyTail.lean`), and the
class-specific `integral_biSup_le_of_forall_finset` of the VC cluster.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Remark 7.2.1 and the p. 227 footnote ("the
general case typically follows by approximation"): these engines are the
approximation step, shared by every countable/separable supremum form of the
chaining batch.

**Proof formalization notes.** No probability hypothesis anywhere — the
engines hold for an arbitrary measure (`B = ⊤` and `C = ∅` branches are
trivial). The tail engines conclude on the **existential** event
`{ω | ∃ i ∈ C, thr < f i ω}`, deliberately junk-free (no real supremum in
the statement); the formal-`⨆` displays are recovered downstream through
`exists_lt_of_lt_biSup_real`, whose `0 ≤ c` hypothesis absorbs the
`Real.sSup ∅ = 0` junk branch. Monotone convergence runs along the prefix
exhaustion `S n := (Finset.range (n+1)).image f` of an enumeration
(`Set.Countable.exists_eq_range`); events use
`tendsto_measure_iUnion_atTop` (measures are continuous from below on
arbitrary monotone sequences). Named-sorry fallback of this work item:
`toReal_biSup_ofReal` (the guarded `ofReal`/`⨆` commutation).

**Bibliographic comments.** The finite-subset reading of `E sup` is standard
in the chaining literature (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, Springer 2014, §2.2); the monotone-convergence lift
to countable index sets is folklore.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Countable-sup lift engine, lintegral form** (sup policy): if every
finite subfamily's `∫⁻`-sup obeys a bound `B : ℝ≥0∞`, so does the countable
family's — monotone convergence along a prefix exhaustion. Index-polymorphic
`ℝ≥0∞` twin of the VC cluster's `integral_biSup_le_of_forall_finset`; no
probability hypothesis, and the `C = ∅` / `B = ⊤` corners are trivial. -/
lemma lintegral_biSup_le_of_forall_finset {ι : Type*} {g : ι → Ω → ℝ≥0∞}
    {C : Set ι}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    -- LEAN-ONLY: a.e.-measurability of each coordinate (MCT)
    (hmeas : ∀ i ∈ C, AEMeasurable (g i) μ)
    {B : ℝ≥0∞}
    -- LEAN-ONLY: the per-finite-subfamily bound being lifted
    (hB : ∀ F : Finset ι, ↑F ⊆ C → F.Nonempty →
      ∫⁻ ω, ⨆ i ∈ F, g i ω ∂μ ≤ B) :
    ∫⁻ ω, ⨆ i ∈ C, g i ω ∂μ ≤ B := by
  sorry

/-- **Countable-sup lift engine, tail form** (sup policy): a uniform
per-finite-window tail bound at a fixed threshold passes to the event that
SOME member of the countable family exceeds the threshold — continuity of
the measure from below along the windows. The existential event is
deliberately junk-free (no real supremum appears); combine with
`exists_lt_of_lt_biSup_real` to bound formal-`⨆` events. -/
lemma measure_exists_lt_le_of_forall_finset {ι : Type*} {f : ι → Ω → ℝ}
    {C : Set ι}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    {thr : ℝ} {β : ℝ≥0∞}
    -- LEAN-ONLY: the per-finite-window tail bound being lifted
    (hB : ∀ (F : Finset ι) (hFne : F.Nonempty), ↑F ⊆ C →
      μ {ω | thr < F.sup' hFne fun i => f i ω} ≤ β) :
    μ {ω | ∃ i ∈ C, thr < f i ω} ≤ β := by
  sorry

/-- Pair variant of `measure_exists_lt_le_of_forall_finset`: per-window
bounds on the product maximum `(F ×ˢ F).sup'` lift to the event that some
PAIR of the countable family exceeds the threshold (the shape of
Eq. (8.15)). -/
lemma measure_exists_pair_lt_le_of_forall_finset {ι : Type*}
    {f : ι → ι → Ω → ℝ} {C : Set ι}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    {thr : ℝ} {β : ℝ≥0∞}
    -- LEAN-ONLY: the per-finite-window pair tail bound being lifted
    (hB : ∀ (F : Finset ι) (hFne : F.Nonempty), ↑F ⊆ C →
      μ {ω | thr < (F ×ˢ F).sup' (hFne.product hFne) fun p => f p.1 p.2 ω}
        ≤ β) :
    μ {ω | ∃ i ∈ C, ∃ j ∈ C, thr < f i j ω} ≤ β := by
  sorry

/-- Finite `⨆ ENNReal.ofReal` as `ENNReal.ofReal` of the Bochner integral of
the `Finset.sup'` carrier: the per-level bridge between the engine's
integrand and the per-finite-subset theorems. The sup'-level sign hypothesis
is sharp — anchored families have negative members but a `0`-valued member
at the anchor. -/
lemma lintegral_biSup_finset_ofReal_eq {ι : Type*} {F : Finset ι}
    (hFne : F.Nonempty) {f : ι → Ω → ℝ}
    -- LEAN-ONLY: nonnegative finite maximum (sharp junk guard)
    (h0 : ∀ ω, 0 ≤ F.sup' hFne fun i => f i ω)
    -- LEAN-ONLY: integrability of the finite maximum (ψ₂ or per-coordinate)
    (hInt : MeasureTheory.Integrable (fun ω => F.sup' hFne fun i => f i ω) μ) :
    ∫⁻ ω, ⨆ i ∈ F, ENNReal.ofReal (f i ω) ∂μ
      = ENNReal.ofReal (∫ ω, F.sup' hFne (fun i => f i ω) ∂μ) := by
  sorry

/-- The guarded infinite `ofReal`/`⨆` commutation: for a nonnegative family
with finite `ℝ≥0∞`-supremum, `toReal` of the `⨆ ENNReal.ofReal` recovers the
real supremum. (Mathlib has no `ENNReal.ofReal_iSup`; the `≠ ⊤` guard is
what makes this true — an unbounded family junks the real side to `0` while
the `ℝ≥0∞` side is honestly `⊤`.) -/
lemma toReal_biSup_ofReal {ι : Type*} {C : Set ι} {h : ι → ℝ}
    -- LEAN-ONLY: nonnegative family (junk alignment)
    (h0 : ∀ i ∈ C, 0 ≤ h i)
    -- LEAN-ONLY: finite ℝ≥0∞ supremum (the commutation guard)
    (htop : (⨆ i ∈ C, ENNReal.ofReal (h i)) ≠ ⊤) :
    (⨆ i ∈ C, ENNReal.ofReal (h i)).toReal = ⨆ i ∈ C, h i := by
  sorry

/-- Strict nonnegative thresholds pierce a real bounded supremum: the `0 ≤ c`
hypothesis absorbs the `Real.sSup` junk value (an unbounded or empty family
junks the supremum to `0 ≤ c`, contradicting the strict inequality). -/
lemma exists_lt_of_lt_biSup_real {ι : Type*} {S : Set ι} {h : ι → ℝ} {c : ℝ}
    -- LEAN-ONLY: nonnegative threshold (absorbs the `Real.sSup ∅ = 0` junk)
    (hc : 0 ≤ c)
    (hlt : c < ⨆ i ∈ S, h i) :
    ∃ i ∈ S, c < h i := by
  sorry

/-- Pair version of `exists_lt_of_lt_biSup_real` for nested double suprema. -/
lemma exists_pair_lt_of_lt_biSup_real {ι : Type*} {S : Set ι}
    {h : ι → ι → ℝ} {c : ℝ}
    -- LEAN-ONLY: nonnegative threshold (absorbs the `Real.sSup ∅ = 0` junk)
    (hc : 0 ≤ c)
    (hlt : c < ⨆ i ∈ S, ⨆ j ∈ S, h i j) :
    ∃ i ∈ S, ∃ j ∈ S, c < h i j := by
  sorry

/-- **Bochner bridge, integrability**: a countable nonnegative family whose
`⨆ ENNReal.ofReal` has finite lintegral has an integrable real supremum
(a.e. finiteness + countable measurability + `toReal_biSup_ofReal`). -/
lemma integrable_biSup_of_lintegral_biSup_ne_top {ι : Type*} {C : Set ι}
    {f : ι → Ω → ℝ}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    -- LEAN-ONLY: a.e.-measurability of each coordinate
    (hmeas : ∀ i ∈ C, AEMeasurable (f i) μ)
    -- LEAN-ONLY: nonnegative family (junk alignment)
    (h0 : ∀ i ∈ C, ∀ ω, 0 ≤ f i ω)
    -- LEAN-ONLY: finite lintegral of the ℝ≥0∞ primary
    (hfin : ∫⁻ ω, ⨆ i ∈ C, ENNReal.ofReal (f i ω) ∂μ ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ C, f i ω) μ := by
  sorry

/-- **Bochner bridge, integral bound**: the real-integral display of a
countable-sup lintegral bound, under the `≠ ⊤` guard. -/
lemma integral_biSup_le_of_lintegral_biSup_le {ι : Type*} {C : Set ι}
    {f : ι → Ω → ℝ}
    -- LEAN-ONLY: countable index family per the sup policy
    (hcnt : C.Countable)
    -- LEAN-ONLY: a.e.-measurability of each coordinate
    (hmeas : ∀ i ∈ C, AEMeasurable (f i) μ)
    -- LEAN-ONLY: nonnegative family (junk alignment)
    (h0 : ∀ i ∈ C, ∀ ω, 0 ≤ f i ω)
    {B : ℝ≥0∞}
    -- LEAN-ONLY: the ℝ≥0∞ primary bound being displayed
    (hB : ∫⁻ ω, ⨆ i ∈ C, ENNReal.ofReal (f i ω) ∂μ ≤ B)
    -- LEAN-ONLY: finite bound so the real display is honest (junk-guard)
    (hBtop : B ≠ ⊤) :
    ∫ ω, ⨆ i ∈ C, f i ω ∂μ ≤ B.toReal := by
  sorry

end StatLean.ConcentrationInequalities
