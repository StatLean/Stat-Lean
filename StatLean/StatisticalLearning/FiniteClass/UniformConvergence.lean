import StatLean.StatisticalLearning.Core.SampleLaw
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded

/-!
# Finite classes have the uniform convergence property

SSBD §4.2: for a finite hypothesis class and a loss with range in `[0,1]`,
Hoeffding's inequality for each fixed hypothesis (SSBD Eq. (4.2), tail
`2 exp(−2nε²)`) plus a union bound (SSBD Eq. (4.1)) gives
`P(∃ h ∈ 𝓗, |L_S(h) − L_D(h)| > ε) ≤ 2|𝓗| exp(−2nε²)`, hence the uniform
convergence property with `m^{UC}(ε,δ) ≤ ⌈log(2|𝓗|/δ)/(2ε²)⌉`
(SSBD Corollary 4.6, first half — exact constants frozen).

**Reference.** SSBD §4.2, Lemma 4.5, Corollary 4.6. Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** The per-hypothesis tail is assembled from the
project's `hoeffding` (`ConcentrationInequalities/SubGaussian/Hoeffding.lean`,
sub-Gaussian sum tail `exp(−n t²/(2σ²))`) with proxy `σ² = 1/4` from
`isSubGaussian_of_mem_Icc` on `[0,1]` — recovering the book's `exp(−2nε²)`
exactly — applied to the coordinate stream of `sampleLaw`
(`iIndepFun_eval_sampleLaw`, `measurePreserving_eval_sampleLaw`), on both the
variables and their negations for the two-sided form. The class is a `Finset H`
so `|𝓗|` is `𝓗.card`.
-/

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal NNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ} {ℓ : H → Z → ℝ}

/-- **Per-hypothesis two-sided Hoeffding deviation** (SSBD Eq. (4.2)): for a
fixed `h` with loss range in `[0,1]`,
`P_{S∼Dⁿ}(|L_S(h) − L_D(h)| > ε) ≤ 2 exp(−2nε²)`. -/
theorem measure_empRisk_deviation_le {h : H} {ε : ℝ}
    -- USER-INPUT: loss range in `[0,1]`; SSBD Cor. 4.6 hypothesis
    (hrange : ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of the loss of `h`; SSBD Remark 3.1
    (hmeas : Measurable (ℓ h))
    -- USER-INPUT: at least one example; SSBD §4.2 (implicit)
    (hn : 1 ≤ n)
    -- USER-INPUT: `ε > 0`; SSBD Lemma 4.5
    (hε : 0 < ε) :
    sampleLaw D n {s | ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * n * ε ^ 2)) := by
  sorry

/-- **Finite-class uniform deviation bound** (SSBD Eq. (4.1) + (4.2)): for a
finite class with `[0,1]`-valued loss,
`P(∃ h ∈ 𝓗, |L_S(h) − L_D(h)| > ε) ≤ 2|𝓗| exp(−2nε²)`. -/
theorem finiteClass_measure_uniformDeviation_le (𝓗 : Finset H) {ε : ℝ}
    -- USER-INPUT: loss range in `[0,1]` on the class; SSBD Cor. 4.6
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of each loss; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h))
    -- USER-INPUT: at least one example; SSBD §4.2 (implicit)
    (hn : 1 ≤ n)
    -- USER-INPUT: `ε > 0`; SSBD Lemma 4.5
    (hε : 0 < ε) :
    sampleLaw D n {s | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal (2 * 𝓗.card * Real.exp (-2 * n * ε ^ 2)) := by
  sorry

/-- **SSBD Corollary 4.6, uniform-convergence half**: a finite class with
`[0,1]`-valued loss has the uniform convergence property with
`m^{UC}(ε,δ) = ⌈log(2|𝓗|/δ)/(2ε²)⌉` (exact book constant). -/
theorem finiteClass_hasUniformConvergenceWith (𝓗 : Finset H)
    -- USER-INPUT: nonempty class; SSBD §4.2 (implicit — else vacuous)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: loss range in `[0,1]` on the class; SSBD Cor. 4.6
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of each loss; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h)) :
    HasUniformConvergenceWith (↑𝓗 : Set H) ℓ
      (fun ε δ => ⌈Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2)⌉₊) := by
  sorry

end StatLean.StatisticalLearning
