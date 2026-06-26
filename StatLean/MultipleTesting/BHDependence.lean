import StatLean.MultipleTesting.BenjaminiHochberg
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Benjamini–Hochberg FDR control under arbitrary dependence — assembly

The Benjamini–Hochberg procedure `bhRejects α p` (defined in `BenjaminiHochberg.lean`: reject
`{ j : pⱼ ≤ k̂α/N }` with `k̂ = max{ k : #{j : pⱼ ≤ kα/N} ≥ k }`) controls FDR **without any
independence assumption** on the p-values, at the cost of a harmonic-number factor.

**Main result** (`benjamini_hochberg_dependent_fdr_le`, Candès, Lecture 5 §5.5 / Lecture 6 §6.6,
Theorem 3, STAT 300C — the Benjamini–Yekutieli bound): if every null p-value is super-uniform
(and the p-values are otherwise **arbitrarily dependent**), then
`FDR ≤ (N₀/N)·α·Hₙ`, where `Hₙ = ∑_{k=1}^N 1/k` is the `N`-th harmonic number and `N₀ = |H₀|`.

Running BH at level `α/Hₙ` therefore controls FDR at `(N₀/N)·α ≤ α` under arbitrary dependence —
the Benjamini–Yekutieli correction.

*Proof (Benjamini–Yekutieli layer-cake).* `FDP = ∑_{i∈H₀} ψᵢ/(R∨1)`; for each null `i`, expand
`ψᵢ/(R∨1) = ∑_{k=1}^N (1/k)·𝟙(R=k)·ψᵢ` and use that on `{R=k}` a rejected `i` has `pᵢ ≤ kα/N`, then
reorganize the double sum (Abel/layer-cake) so each null contributes `≤ (α/N)·Hₙ` using only
super-uniformity `P(pᵢ ≤ kα/N) ≤ kα/N` — no factorization, hence no independence needed. Summing
over `H₀` gives `(N₀/N)·α·Hₙ`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Benjamini–Hochberg FDR control under arbitrary dependence** (Candès, Lecture 5 §5.5 /
Lecture 6 §6.6, Theorem 3, STAT 300C — Benjamini–Yekutieli). With every null p-value super-uniform
and **no independence assumption**, the BH procedure at level `α` has
`FDR ≤ (N₀/N)·α·Hₙ`, `Hₙ` the `N`-th harmonic number, `N₀ = |H₀|`. -/
theorem benjamini_hochberg_dependent_fdr_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L5/L6
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: every null p-value is super-uniform; Candès L5/L6 Thm 3.
    -- NOTE: no independence hypothesis — this is the arbitrary-dependence theorem.
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FDR H₀ (bhRejects α p) μ ≤ (H₀.card : ℝ) / N * α * (harmonic N : ℝ) := by
  sorry

end StatLean.MultipleTesting
