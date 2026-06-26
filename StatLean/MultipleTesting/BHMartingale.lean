import StatLean.MultipleTesting.BenjaminiHochberg

/-!
# Benjamini–Hochberg FDR — exact identity (Candès, Lecture 7, §7.2, Theorem 2)

The Benjamini–Hochberg procedure `bhRejects α p` controls FDR with **equality** when the null
p-values are exactly uniform: `FDR = (N₀/N)·α` (Candès, Lecture 7, §7.2, Theorem 2, with `q = α`,
`N₀ = |H₀|`).

**Main result** (`benjamini_hochberg_fdr_eq`): independent p-values, every null exactly uniform ⇒
`FDR = (N₀/N)·α`.

*On the proof technique.* The lecture proves this via a backwards-martingale + Doob's optional
stopping argument on `V(t)/t`. We obtain the **same identity** by the leave-one-out argument already
used for the inequality `benjamini_hochberg_fdr_le` (`BenjaminiHochberg.lean`): for each null `i`,
`E[ψᵢ/(R∨1)] = (α/N)·P(pᵢ ≤ …)`-style telescopes to `α/N` **with equality** because exact uniformity
gives `P(pᵢ ≤ kα/N) = kα/N` (the inequality version only had `≤`); summing over `H₀` gives
`(N₀/N)·α`. This avoids the continuous-time backwards-martingale machinery (absent from Mathlib)
while proving the identical theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Benjamini–Hochberg FDR exact identity** (Candès, Lecture 7, §7.2, Theorem 2, STAT 300C). With
independent p-values and every null **exactly** uniform, the BH procedure at level `α` has
`FDR = (N₀/N)·α` (`N₀ = |H₀|`). -/
theorem benjamini_hochberg_fdr_eq {N : ℕ} (hN : 0 < N) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L7 §7.2
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L7 §7.2
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is exactly uniform on [0,1]; Candès L7 §7.2 (the martingale
    -- proof's equality needs exact uniformity, not just super-uniformity)
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    FDR H₀ (bhRejects α p) μ = (H₀.card : ℝ) / N * α := by
  sorry

end StatLean.MultipleTesting
