import StatLean.StatisticalLearning.Rademacher.Defs
import StatLean.StatisticalLearning.Core.SampleLaw
import StatLean.ConcentrationInequalities.VC.SauerShelah

/-!
# Boolean classifiers ↔ set classes: the VC dictionary

The bridge between this area's learning-theoretic data model (predictors
`h : X → Bool`, 0–1 loss on pairs `X × Bool`, `risk`/`empRisk`) and the
set-class VC machinery of `ConcentrationInequalities/VC/` (`Shatters`,
`vcDim`, `traceFamily`, `empFrac` on `Set X`): the positive-set encoding of a
predictor class, the pair-space error set of a predictor, the risk/empirical
risk dictionaries, and the Sauer–Shelah trace count for the evaluated loss
family `{(𝟙[h(xᵢ)≠yᵢ])ᵢ : h ∈ 𝓗}` (SSBD §28.1 step 1: the loss vectors are
an XOR-mask of the trace vectors, so their number is bounded by the growth
function).

**Reference.** SSBD Definitions 6.2/6.3/6.5/6.9, Lemma 6.10, and §28.1
step 1. Transcriptions: `notes/statistical_learning/book_statements/ch6-28.md`.

**Formalization notes.** VC hypotheses downstream are phrased as
`vcDim (setClassOf 𝓗) ≤ d` — no new Boolean `vcDim` is introduced. The trace
bound deliberately avoids `growthFunction` (whose `ℕ∞` sup is junk `0` when
`X` has fewer than `n` points) and goes through `traceFamily` on the sample's
instance `Finset` directly, then Sauer–Shelah
(`ConcentrationInequalities/VC/SauerShelah.lean`).
-/

open MeasureTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {X : Type*} {n : ℕ}

/-- The positive-set encoding of a Boolean predictor class (SSBD's
identification of `h : X → {0,1}` with `{x | h(x) = 1}`). -/
def setClassOf (𝓗 : Set (X → Bool)) : Set (Set X) :=
  (fun h => {x | h x = true}) '' 𝓗

/-- The pair-space error set of a predictor: `{(x,y) | h(x) ≠ y}` — the 0–1
loss of `h` is its indicator (SSBD Eq. (3.1)). -/
def errSet (h : X → Bool) : Set (X × Bool) :=
  {p | h p.1 ≠ p.2}

/-- Risk dictionary: the 0–1 risk is the mass of the error set
(SSBD Eq. (3.1) vs Eq. (3.3), "the definitions coincide"). -/
theorem risk_zeroOneLoss_eq [MeasurableSpace X] (D : Measure (X × Bool))
    [IsProbabilityMeasure D] (h : X → Bool)
    -- USER-INPUT: measurable error set; SSBD Remark 3.1 (0–1-loss form)
    (hmeas : MeasurableSet (errSet h)) :
    risk D zeroOneLoss h = D.real (errSet h) := by
  sorry

/-- Empirical-risk dictionary: the empirical 0–1 risk is the empirical
fraction of the error set (SSBD Eq. (2.2) vs `empFrac`); pure algebra. -/
theorem empRisk_zeroOneLoss_eq (s : Sample (X × Bool) n) (h : X → Bool) :
    empRisk zeroOneLoss s h = empFrac s (errSet h) := by
  sorry

/-- The evaluated 0–1 loss family is finite: loss vectors take values in
`{0,1}ⁿ` (LEAN-ONLY; feeds the `Finset`-typed Massart lemma). -/
theorem finite_evalFamily_zeroOneLoss (𝓗 : Set (X → Bool))
    (s : Sample (X × Bool) n) :
    (evalFamily zeroOneLoss 𝓗 s).Finite := by
  sorry

/-- **Loss-pattern count via Sauer–Shelah** (SSBD §28.1 step 1): if
`vcDim (setClassOf 𝓗) ≤ d`, the number of distinct loss vectors
`{(𝟙[h(xᵢ)≠yᵢ])ᵢ : h ∈ 𝓗}` on any `n`-sample is at most
`∑_{j=0}^d C(n,j)` — the XOR mask `y` identifies loss vectors with trace
vectors, and the trace count is Sauer–Shelah's. -/
theorem ncard_evalFamily_zeroOneLoss_le (𝓗 : Set (X → Bool)) {d : ℕ}
    (s : Sample (X × Bool) n)
    -- USER-INPUT: VC dimension bound; SSBD Lemma 6.10
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞)) :
    (evalFamily zeroOneLoss 𝓗 s).ncard ≤
      ∑ j ∈ Finset.range (d + 1), n.choose j := by
  sorry

/-- **Polynomial loss-pattern count** (SSBD Lemma 6.10 second half /
Lemma A.5): for `1 ≤ d` and `d + 1 < n`, the loss-pattern count is at most
`(en/d)^d`. -/
theorem ncard_evalFamily_zeroOneLoss_le_pow (𝓗 : Set (X → Bool)) {d : ℕ}
    (s : Sample (X × Bool) n)
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 (nondegenerate class)
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `d + 1 < n`; SSBD Lemma 6.10 (`m > d + 1`)
    (hn : d + 1 < n) :
    ((evalFamily zeroOneLoss 𝓗 s).ncard : ℝ) ≤
      (Real.exp 1 * n / d) ^ d := by
  sorry

end StatLean.StatisticalLearning
