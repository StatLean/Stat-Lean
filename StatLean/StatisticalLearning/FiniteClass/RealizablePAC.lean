import StatLean.StatisticalLearning.Core.SampleLaw

/-!
# Finite classes are PAC learnable in the realizable case

SSBD Ch. 2: under realizability, a hypothesis with true error `> ε` survives
with zero empirical error only with probability `≤ (1−ε)ⁿ ≤ e^{−εn}`
(SSBD Eqs. (2.8)–(2.9)); a union bound over the bad hypotheses gives
`P(∃ ERM h_S with L_{D,f}(h_S) > ε) ≤ |𝓗| e^{−εn}` (SSBD Cor. 2.3, no factor
2, no ceiling), hence PAC learnability with `m(ε,δ) ≤ ⌈log(|𝓗|/δ)/ε⌉`
(SSBD Cor. 3.2, ceiling explicit).

**Reference.** SSBD §2.3, Corollary 2.3; §3.1, Corollary 3.2. Transcriptions:
`notes/statistical_learning/book_statements/ch2-5.md`.

**Formalization notes.** `{s | ∀ i, h (s i) = f (s i)}` is a product cylinder,
so its `sampleLaw` mass is `(D.real {x | h x = f x})^n` exactly (`Measure.pi`
on a product set); `1 − ε ≤ e^{−ε}` finishes Eq. (2.9). The realizability
witness `h⋆` has `L_S(h⋆) = 0` a.s. (SSBD footnote 3, p. 17), which is why
every ERM hypothesis has zero empirical risk a.s. — the a.s. qualifier the
book elides is carried explicitly through the event algebra here.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {X : Type*} [MeasurableSpace X] {D : Measure X}
  [IsProbabilityMeasure D] {n : ℕ} {f : X → Bool}

/-- **Survival probability of a bad hypothesis** (SSBD Eqs. (2.8)–(2.9)): if
`L_{D,f}(h) > ε` then `h` is consistent with the labeled sample with
probability at most `(1−ε)ⁿ ≤ e^{−εn}`. -/
theorem measure_consistent_le_of_errProb_gt {h : X → Bool} {ε : ℝ}
    -- USER-INPUT: measurable disagreement set; SSBD Remark 3.1
    (hmeas : MeasurableSet {x | h x ≠ f x})
    -- USER-INPUT: `h` is `ε`-bad; SSBD p. 18 (`h ∈ 𝓗_B`)
    (hbad : ε < errProb D f h)
    -- USER-INPUT: `ε > 0`; SSBD Cor. 2.3
    (hε : 0 < ε) :
    sampleLaw D n {s | ∀ i, h (s i) = f (s i)} ≤
      ENNReal.ofReal (Real.exp (-ε * n)) := by
  sorry

/-- **SSBD Corollary 2.3** (finite classes generalize, realizable case): for
`m ≥ log(|𝓗|/δ)/ε`, with probability `≥ 1 − δ` every consistent hypothesis —
in particular every ERM hypothesis, since realizability makes some `h⋆ ∈ 𝓗`
consistent a.s. — has true error `≤ ε`. Stated as the book does via the bad
event: `P(∃ h ∈ 𝓗 consistent with L_{D,f}(h) > ε) ≤ |𝓗| e^{−εm} ≤ δ`. -/
theorem finiteClass_realizable_uniform (𝓗 : Finset (X → Bool)) {ε δ : ℝ}
    -- USER-INPUT: measurable disagreement sets; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, MeasurableSet {x | h x ≠ f x})
    -- USER-INPUT: `ε > 0`; SSBD Cor. 2.3
    (hε : 0 < ε)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Cor. 2.3
    (hδ : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: sample size `m ≥ log(|𝓗|/δ)/ε` (no ceiling — the book's
    -- "any integer satisfying"); SSBD Cor. 2.3
    (hn : Real.log (𝓗.card / δ) / ε ≤ n) :
    sampleLaw D n
        {s | ∃ h ∈ 𝓗, (∀ i, h (s i) = f (s i)) ∧ ε < errProb D f h} ≤
      ENNReal.ofReal δ := by
  sorry

/-- **SSBD Corollary 3.2** (finite classes are PAC learnable): any ERM selector
PAC-learns a finite class with sample complexity `⌈log(|𝓗|/δ)/ε⌉` (ceiling
explicit, as in the book's restatement of Cor. 2.3). -/
theorem finiteClass_isPACLearnerWith (𝓗 : Finset (X → Bool))
    {A : ∀ m : ℕ, Sample (X × Bool) m → (X → Bool)}
    -- USER-INPUT: nonempty class; SSBD §2.3 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: measurable disagreement sets against every target;
    -- SSBD Remark 3.1 (0–1-loss instantiation)
    (hmeas : ∀ (g : X → Bool), ∀ h ∈ 𝓗, MeasurableSet {x | h x ≠ g x})
    -- USER-INPUT: `A` is an ERM selector for the 0–1 loss; SSBD §2.3
    (hA : ∀ (m : ℕ) (s : Sample (X × Bool) m),
      IsERM (↑𝓗 : Set (X → Bool)) zeroOneLoss s (A m s)) :
    IsPACLearnerWith (↑𝓗 : Set (X → Bool)) A
      (fun ε δ => ⌈Real.log (𝓗.card / δ) / ε⌉₊) := by
  sorry

end StatLean.StatisticalLearning
