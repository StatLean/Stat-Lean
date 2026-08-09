import StatLean.StatisticalLearning.VC.Bridge
import StatLean.StatisticalLearning.Rademacher.Structural
import StatLean.StatisticalLearning.Rademacher.Generalization
import StatLean.StatisticalLearning.Core.ERM

/-!
# Finite VC dimension ⇒ agnostic PAC learnability (upper bound)

The agnostic upper bound of the Fundamental Theorem of learning theory
(SSBD Theorem 6.7 direction 6→1→2→3; Theorem 6.8 items 1–2 up to the book's
own `log(d/ε)` looseness), by the Massart route of SSBD §28.1:

* Sauer–Shelah bounds the loss-pattern count by `(en/d)^d` (`VC/Bridge`);
* Massart's lemma turns that into `R(𝓕∘S) ≤ √(2d log(en/d)/n)` pointwise;
* Theorem 26.5(1) on the loss family and its negation plus a union bound give,
  w.p. `≥ 1 − δ`: `∀h ∈ 𝓗, |L_D(h) − L_S(h)| ≤ √(8d log(en/d)/n) +
  √(2 log(4/δ)/n)` (SSBD §28.1 step 4);
* the log-inversion Lemma A.2 yields the explicit sufficient sample size
  `m ≥ (128d/ε²)·log(64d/ε²) + (8/ε²)(8d log(e/d) + 2 log(4/δ))`
  (SSBD p. 341, exact constants frozen).

**Reference.** SSBD §28.1; Lemma A.2. Transcriptions:
`notes/statistical_learning/book_statements/ch6-28.md`.

**Formalization notes.** `Countable 𝓗` is LEAN-ONLY per the batch sup policy
(the book quantifies over arbitrary classes); the `StandardBorelSpace X`
instance is inherited from the McDiarmid engine behind Theorem 26.5. The VC
hypothesis is `vcDim (setClassOf 𝓗) ≤ d` (set-class dictionary). This is the
`log(d/ε)`-loose form the book actually proves — the tight `d/ε²` of
Theorem 6.8 requires chaining and is out of scope (SSBD's own remark). -/

open MeasureTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  {n : ℕ} {d : ℕ}

/-- **SSBD Lemma A.2** (log inversion): for `a ≥ 1`, `b > 0`, every
`x ≥ 4a log(2a) + 2b` satisfies `x ≥ a log x + b`. -/
theorem ge_log_bound_of_ge (a b x : ℝ)
    -- USER-INPUT: `a ≥ 1`; SSBD Lemma A.2
    (ha : 1 ≤ a)
    -- USER-INPUT: `b > 0`; SSBD Lemma A.2
    (hb : 0 < b)
    (hx : 4 * a * Real.log (2 * a) + 2 * b ≤ x) :
    a * Real.log x + b ≤ x := by
  sorry

/-- **Pointwise VC bound on the empirical Rademacher complexity**
(SSBD §28.1 step 2): if `vcDim (setClassOf 𝓗) ≤ d`, `1 ≤ d`, `d + 1 < n`,
then for every sample, `R(ℓ₀₁∘𝓗∘S) ≤ √(2 d log(en/d)/n)`. -/
theorem vc_empRad_le (𝓗 : Set (X → Bool)) (s : Sample (X × Bool) n)
    -- USER-INPUT: nonempty class; SSBD §28.1 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: VC dimension bound; SSBD Thm 6.8 / §28.1
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 side condition
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `d + 1 < n`; SSBD Lemma 6.10 (`m > d + 1`)
    (hn : d + 1 < n) :
    empRad zeroOneLoss 𝓗 s ≤
      Real.sqrt (2 * d * Real.log (Real.exp 1 * n / d) / n) := by
  sorry

/-- **VC uniform deviation, high probability** (SSBD §28.1 step 4): for a
countable class of VC dimension `≤ d`, with probability `≥ 1 − δ`,
simultaneously for every `h ∈ 𝓗`,
`|L_D(h) − L_S(h)| ≤ √(8 d log(en/d)/n) + √(2 log(4/δ)/n)`. -/
theorem vc_uniformDeviation_hp (𝓗 : Set (X → Bool))
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] {δ : ℝ}
    -- LEAN-ONLY: countable class per the batch sup policy
    (hc : 𝓗.Countable)
    -- USER-INPUT: nonempty class; SSBD §28.1 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: measurable error sets; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, MeasurableSet (errSet h))
    -- USER-INPUT: VC dimension bound; SSBD Thm 6.8 / §28.1
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 side condition
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `d + 1 < n`; SSBD Lemma 6.10 (`m > d + 1`)
    (hn : d + 1 < n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD §28.1
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ h ∈ 𝓗,
        |empRisk zeroOneLoss s h - risk D zeroOneLoss h| ≤
          Real.sqrt (8 * d * Real.log (Real.exp 1 * n / d) / n) +
            Real.sqrt (2 * Real.log (4 / δ) / n)} := by
  sorry

/-- **Finite VC dimension ⇒ agnostic PAC learnability by ERM**
(SSBD Theorem 6.7, 6→3; §28.1 headline with the explicit sample size of
p. 341): any ERM selector agnostically PAC-learns a countable class of VC
dimension `≤ d` with sample complexity
`m(ε,δ) = ⌈(128d/ε²) log(64d/ε²) + (8/ε²)(8d log(e/d) + 2 log(4/δ))⌉ + d + 2`
(the `+ d + 2` enforces Sauer's `m > d + 1` side condition; book constants
otherwise frozen). -/
theorem vc_isAgnosticPACLearnerWith (𝓗 : Set (X → Bool))
    {A : ∀ m : ℕ, Sample (X × Bool) m → (X → Bool)}
    -- LEAN-ONLY: countable class per the batch sup policy
    (hc : 𝓗.Countable)
    -- USER-INPUT: nonempty class; SSBD §28.1 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: measurable error sets; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, MeasurableSet (errSet h))
    -- USER-INPUT: VC dimension bound; SSBD Thm 6.8
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 side condition
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `A` is an ERM selector; SSBD §28.1 ("applying the ERM rule")
    (hA : ∀ (m : ℕ) (s : Sample (X × Bool) m),
      IsERM 𝓗 zeroOneLoss s (A m s)) :
    IsAgnosticPACLearnerWith 𝓗 zeroOneLoss A
      (fun ε δ =>
        ⌈128 * d / ε ^ 2 * Real.log (64 * d / ε ^ 2) +
            8 / ε ^ 2 * (8 * d * Real.log (Real.exp 1 / d) +
              2 * Real.log (4 / δ))⌉₊ + d + 2) := by
  sorry

end StatLean.StatisticalLearning
