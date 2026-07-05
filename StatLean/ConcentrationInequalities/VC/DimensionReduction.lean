import StatLean.ConcentrationInequalities.VC.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded
import Mathlib.Probability.Independence.Basic

/-!
# Dimension reduction: ε-separation survives empirical projection

Let $S_1, \dots, S_N$ ($N = |\mathcal{F}| \ge 2$) be measurable sets that are
$\varepsilon$-separated in $L^2(\mu)$ in the squared sense
$\mu(S \bigtriangleup T) > \varepsilon^2$ for all pairs $S \ne T$, and let
$X_1, X_2, \dots$ be i.i.d. with law $\mu$. If
$n \ge 100\,\varepsilon^{-4}\log|\mathcal{F}|$, then with probability at
least $0.99$ the family stays $\varepsilon/2$-separated in $L^2(\mu_n)$:
$$ \mathbb{P}\Bigl\{\exists\, S \ne T \in \mathcal{F} :
   \mu_n(S \bigtriangleup T) \le \varepsilon^2/4 \Bigr\} \;\le\; 1/100. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.5, Lemma 8.3.14 (stated in squared-distance
form: net radius `ε` ⟺ measure ≤ `ε²`, separation ⟺ `> ε²`).

**Proof formalization notes.** Per-pair concentration reuses the existing
`hoeffding` (ℕ-indexed, `Finset.range n`, `μ.real` conclusion) applied
one-sided to the *negated* indicators
`Y i ξ := −(S ∆ T).indicator 1 (X i ξ)`: each `Y i` takes values in
`[−1, 0]`, hence is `IsSubGaussian` with proxy `(1/2)²` via
`isSubGaussian_of_mem_Icc`, giving
`P{empFrac ≤ μ.real(S∆T) − t} ≤ exp(−2·n·t²)`. Applying it at the deviation
`t = (3/4)ε²` (from separation `> ε²` down to threshold `ε²/4`) gives
`exp(−(9/8)·n·ε⁴)` per ordered pair; the union bound over at most `|F|²`
ordered pairs plus the numeric fact `100·log 2 ≥ 2·log|F|/log|F| …` slack
(`log 100 ≤ 5`, one-sided Hoeffding needs only `≈ 8·ε⁻⁴·log|F|` samples, so
the book's sample-size constant `C = 100` is provable with large slack)
closes the bound `≤ 1/100`. Union-bound measurability: only the per-pair
Hoeffding event needs to be measurable, which it is since `S, T` are.
Identical distribution is encoded as the map equality `P.map (X i) = μ`
(the pin's `ProbabilityTheory.HasLaw` is not used, per the batch's frozen
interface). Constants: failure probability `1/100` and sample-size constant
`100` are the book's. Named-sorry fallback of this work item:
`dimension_reduction` (keep `empFrac_symmDiff_concentration_pair` — the
Hoeffding reuse — real; sorry only the union-bound + numeric assembly).

**Bibliographic comments.** The dimension-reduction step is the modern
streamlining (due to Vershynin, HDP §8.3.5) of the random-projection idea in
the covering-number bound of R. M. Dudley, "Central limit theorems for
empirical measures," *Ann. Probab.* 6 (1978), 899–929; see HDP §8.3 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Numeric helper: `log 100 ≤ 5` (LEAN-ONLY: `exp 5 ≥ 100` via
`Real.exp_one_gt_d9`). -/
private lemma log_hundred_le_five : Real.log 100 ≤ 5 := by
  sorry

/-- Per-pair one-sided concentration of the empirical measure of a symmetric
difference (HDP §8.3.5, Lemma 8.3.14 proof step): the empirical fraction of
`S ∆ T` undershoots its mean by `t` with probability at most
`exp(−2·n·t²)` — the existing `hoeffding` applied to the negated indicators,
sub-Gaussian with proxy `(1/2)²` via `isSubGaussian_of_mem_Icc`. -/
lemma empFrac_symmDiff_concentration_pair {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; needed to lift
    -- independence through the indicator composition, no scope change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.5,
    -- Lemma 8.3.14 ("i.i.d.").
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.5, Lemma 8.3.14 (stated as a
    -- map equality; `ProbabilityTheory.HasLaw` not used per batch interface).
    (hlaw : ∀ i, P.map (X i) = μ)
    {S T : Set Ω}
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    {t : ℝ}
    -- USER-INPUT: positive deviation level; HDP §8.3.5, Lemma 8.3.14 proof.
    (ht : 0 < t)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.5 (implicit).
    (hn : 1 ≤ n) :
    P {ξ | empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ μ.real (S ∆ T) - t}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  sorry

/-- **Dimension reduction** (HDP §8.3.5, Lemma 8.3.14, squared-distance
form): an `ε`-separated finite family (`μ(S ∆ T) > ε²` for `S ≠ T`) stays
`ε/2`-separated in `L²(μ_n)` (`μ_n(S ∆ T) > ε²/4`) with probability at least
`0.99`, once `n ≥ 100·ε⁻⁴·log|F|`. -/
theorem dimension_reduction {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity, no scope
    -- change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.5,
    -- Lemma 8.3.14.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.5, Lemma 8.3.14 (map form).
    (hlaw : ∀ i, P.map (X i) = μ)
    (F : Finset (Set Ω))
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    -- USER-INPUT: at least two sets, so there is a pair to separate;
    -- HDP §8.3.5, Lemma 8.3.14 (implicit in "ε-separated").
    (hF2 : 2 ≤ F.card)
    {ε : ℝ}
    -- USER-INPUT: positive separation radius; HDP §8.3.5, Lemma 8.3.14.
    (hε : 0 < ε)
    -- USER-INPUT: ε-separation in L²(μ), squared form; HDP §8.3.5,
    -- Lemma 8.3.14.
    (hsep : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ε ^ 2 < μ.real (S ∆ T))
    {n : ℕ}
    -- USER-INPUT: sample-size condition n ≥ 100·ε⁻⁴·log|F|; HDP §8.3.5,
    -- Lemma 8.3.14 (book's unnamed constant committed as C = 100).
    (hn : 100 * ε⁻¹ ^ 4 * Real.log F.card ≤ n) :
    P {ξ | ∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧
        empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ ε ^ 2 / 4}
      ≤ ENNReal.ofReal (1 / 100) := by
  sorry

end StatLean.ConcentrationInequalities
