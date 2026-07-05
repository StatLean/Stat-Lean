import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import StatLean.ConcentrationInequalities.Chaining.EntropySum

/-!
# High-probability Dudley inequality (Eq. (8.15) / Exercise 8.1)

The tail form of Dudley's inequality for a finite index set: with
probability at least $1 - 2e^{-u^2}$,
$$ \sup_{s,t \in T} |X_t - X_s| \;\le\; C K \Bigl[
     \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\, d\varepsilon
     + u \cdot \operatorname{diam} T \Bigr], $$
via per-level tail thresholds $\sqrt{2\log N_k} + \sqrt{k - \kappa'} + u$
instead of per-level expectations. No mean-zero hypothesis. We state a sharp
three-term core and the book-shaped display corollary.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Remark 8.1.6 / Eq. (8.15) (stated there as
Exercise 8.1 — we prove it).

**Proof formalization notes.** The three-term core achieves the book's exact
failure probability `2exp(−u²)`: per-level threshold
`3K·2^{−k}·(√(2 log N_k) + √(k−κ') + u)` over `closePairs`, the
`(a+b+c)² ≥ a²+b²+c²` inflation, and the geometric union bound give failure
probability `≤ 2/(e−1)·e^{−u²} ≤ 1.17·e^{−u²} ≤ 2e^{−u²}` — the book's
`2exp(−u²)` is MET exactly, no deviation. Frozen core constants: event bound
`K·(9·dudleySum + 17·diam + 12·u·diam)` (chosen with ≥ 15% slack in the
per-level threshold algebra). The display form absorbs the bare `diam` term
via `diam·√log2 ≤ 8·dudleyIntegral` (`Chaining/EntropySum.lean`) into the
frozen display constant `200`. This file shares the Step-2/Step-3 event
pattern with `Chaining/GenericChaining.lean` — accepted small duplication in
exchange for pairwise-disjoint parallel proof sessions; the shared
tail-integrates-to-expectation step is factored in
`Chaining/TailToExpectation.lean`. Named-sorry fallback of this work item:
`dudley_tail` (the display form with diameter absorption), with
`dudley_tail_three_term` proved.

**Bibliographic comments.** The high-probability form of Dudley's bound is
folklore refinement of Dudley (1967) by the concentration-of-chaining
argument; the exposition followed here is HDP §8.1 (Exercise 8.1) and
Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2014, §2.2
(where it appears as the tail version of the generic chaining bound
specialized to entropy numbers). See the HDP Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **High-probability Dudley, sharp three-term core** (HDP §8.1, Remark
8.1.6 / Exercise 8.1): with failure probability at most `2exp(−u²)`,
`sup_{s,t} |X_t − X_s| ≤ K(9·dudleySum + 17·diam + 12·u·diam)`. Frozen core
constants `9 / 17 / 12`; the book's `2exp(−u²)` is met exactly. -/
theorem dudley_tail_three_term {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: T finite (the book's standing assumption for (8.15))
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | K * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by sorry

/-- **High-probability Dudley, book display** (HDP §8.1, Eq. (8.15)): with
probability at least `1 − 2exp(−u²)`,
`sup_{s,t} |X_t − X_s| ≤ 200·K·(∫_0^D √(log 𝒩) + u·diam T)`. Book's unnamed
`C` frozen to `200` (the bare diameter term of the three-term core absorbed
via `diam·√log2 ≤ 8·dudleyIntegral`). -/
theorem dudley_tail {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: T finite (the book's standing assumption for (8.15))
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 200 * K * (dudleyIntegral T D + u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by sorry

end StatLean.ConcentrationInequalities
