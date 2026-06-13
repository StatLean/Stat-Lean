import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import Mathlib.Probability.Independence.Basic

/-!
# Benjamini–Hochberg FDR control — assembly (Lu-BDA §18, Theorem `BH`)

The Benjamini–Hochberg procedure at level `α` orders the p-values `p₍₁₎ ≤ ⋯ ≤ p₍N₎`, finds
`iₘₐₓ = max{ i : p₍ᵢ₎ ≤ iα/N }`, and rejects the `iₘₐₓ` smallest. Equivalently (sort-free, the
form used here) it rejects `{ j : pⱼ ≤ k̂·α/N }` where
`k̂ = max{ k ≤ N : #{ j : pⱼ ≤ kα/N } ≥ k }`.

**Main result** (`benjamini_hochberg_fdr_le`): if the p-values are independent and every null
p-value is super-uniform, then `FDR ≤ (N₀/N)·α ≤ α`, where `N₀ = |H₀|`.

*Book vs Lean.* Lu-BDA §18 states the equality `FDR = (N₀/N)·α` for exactly-uniform nulls; we
prove the honest inequality `≤`, which holds under the weaker `SuperUniform` hypothesis and
specializes to the book's equality when the nulls are exactly uniform.

Proof outline (Lu-BDA §18): for `i ∈ H₀`, `E[ψᵢ/(R∨1)] ≤ α/N` (`bh_claim`), via the
leave-one-out invariance `bh_count_eq_leaveOneOut` and the tower property over the σ-algebra of
the other p-values; summing over `i ∈ H₀` gives the bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- Benjamini–Hochberg rejection set at level `α` (Lu-BDA §18): reject `{ j : pⱼ ≤ k̂·α/N }`,
where `k̂ = max{ k ≤ N : #{ j : pⱼ ≤ kα/N } ≥ k }` (the sort-free form of `iₘₐₓ`). With no `k ≥ 1`
satisfying the count condition, `k̂ = 0` and nothing is rejected. -/
noncomputable def bhRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : Finset (Fin N) :=
  let kmax := ((Finset.range (N + 1)).filter
    (fun m => m ≤ (Finset.univ.filter (fun j => p j ω ≤ (m : ℝ) * α / N)).card)).sup id
  Finset.univ.filter (fun j => p j ω ≤ (kmax : ℝ) * α / N)

/-- Leave-one-out invariance (Lu-BDA §18, BH proof, "second key observation"): if hypothesis `i`
is rejected and the total number of rejections is `k`, then replacing `pᵢ` by the constant `0`
leaves the number of rejections equal to `k`. The deterministic combinatorial crux. -/
theorem bh_count_eq_leaveOneOut {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (i : Fin N) (k : ℕ) (ω : Ω)
    (hmem : i ∈ bhRejects α p ω) (hR : numRejections (bhRejects α p) ω = k) :
    numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k := by
  sorry

/-- Per-null contribution bound (Lu-BDA §18, the claim `E[ψᵢ/(R∨1)] = α/N`, honest `≤` form):
for a null index `i` with super-uniform p-value, `E[ψᵢ/(R∨1)] ≤ α/N`. -/
theorem bh_claim {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for independence / integration
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: p-values independent; Lu-BDA §18 (BH)
    (hindep : iIndepFun p μ)
    (i : Fin N)
    -- USER-INPUT: null marginal super-uniform; Lu-BDA §18 (BH)
    (hi : SuperUniform (p i) μ) :
    ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0)
          / max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ ≤ α / N := by
  sorry

/-- **Benjamini–Hochberg FDR control** (Lu-BDA §18, Theorem `BH`). If the p-values are
independent and each null p-value is super-uniform, the BH procedure at level `α` controls the
false discovery rate: `FDR ≤ (N₀/N)·α ≤ α`. -/
theorem benjamini_hochberg_fdr_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for independence / integration
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: p-values independent; Lu-BDA §18 (BH)
    (hindep : iIndepFun p μ)
    -- USER-INPUT: null marginals super-uniform; Lu-BDA §18 (BH)
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FDR H₀ (bhRejects α p) μ ≤ (H₀.card : ℝ) / N * α := by
  sorry

end StatLean.MultipleTesting
