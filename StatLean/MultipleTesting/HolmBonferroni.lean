import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import StatLean.MultipleTesting.ForMathlib.OrderStatistics

/-!
# Holm–Bonferroni FWER control — assembly

**Note on the source.** Lu, *Big Data Analysis* states the plain Bonferroni correction (§17) but
contains *no* Holm step-down theorem. The Holm result is therefore formalized from the standard
statement: S. Holm, "A simple sequentially rejective multiple test procedure", *Scand. J.
Statist.* **6** (1979), 65–70. Hypotheses sourced to Holm (1979) are tagged accordingly.

The Holm step-down procedure orders the p-values `p₍₁₎ ≤ ⋯ ≤ p₍N₎`, walks down comparing
`p₍ᵢ₎` to the cutoff `α/(N−i+1)`, and rejects the initial run that stays below cutoff.

**Main result** (`holm_fwer_le`): if every null p-value is super-uniform (no independence needed),
the Holm procedure controls the family-wise error rate, `FWER ≤ α`.

**Bonferroni corollary** (`bonferroni_fwer_le`, Lu-BDA §17): rejecting `{ j : pⱼ ≤ α/N }` gives
`FWER ≤ (N₀/N)·α ≤ α`.

Proof outline: the deterministic crux `holm_rejects_true_null_imp` shows that if Holm rejects any
true null then some true null has `pⱼ ≤ α/N₀`; a union bound over `H₀` plus super-uniformity
yields `FWER ≤ N₀·(α/N₀) = α`.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- Number of hypotheses Holm rejects: the largest prefix length `k` of the sorted p-values such
that `p₍ᵢ₎ ≤ α/(N−i)` for every `0 ≤ i < k` (0-indexed step-down cutoffs). -/
noncomputable def holmCount {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : ℕ :=
  ((Finset.range (N + 1)).filter
    (fun k => ∀ i : Fin N, (i : ℕ) < k →
      orderStat (fun j => p j ω) i ≤ α / ((N : ℝ) - (i : ℝ)))).sup id

open scoped Classical in
/-- Holm rejection set: the `holmCount` smallest p-values, i.e. those whose rank (number of
strictly smaller p-values) is below the step-down length. -/
noncomputable def holmRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : Finset (Fin N) :=
  Finset.univ.filter
    (fun j => (Finset.univ.filter (fun j' => p j' ω < p j ω)).card < holmCount α p ω)

open scoped Classical in
/-- Bonferroni rejection set (Lu-BDA §17): reject `{ j : pⱼ ≤ α/N }`. -/
noncomputable def bonferroniRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : Finset (Fin N) :=
  Finset.univ.filter (fun j => p j ω ≤ α / (N : ℝ))

/-- Deterministic crux (Holm 1979): if the Holm procedure rejects any true null, then some true
null has p-value `≤ α/N₀`, where `N₀ = |H₀|`. -/
theorem holm_rejects_true_null_imp {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (H₀ : Finset (Fin N))
    (ω : Ω) (hne : ((holmRejects α p ω) ∩ H₀).Nonempty) :
    ∃ j ∈ H₀, p j ω ≤ α / (H₀.card : ℝ) := by
  sorry

/-- **Holm–Bonferroni FWER control** (Holm 1979). If every null p-value is super-uniform, the
Holm step-down procedure at level `α` controls the family-wise error rate: `FWER ≤ α`. No
independence assumption is required. -/
theorem holm_fwer_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (hH₀ : H₀.Nonempty) (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for the union bound over events
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: null marginals super-uniform; Holm (1979)
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FWER H₀ (holmRejects α p) μ ≤ ENNReal.ofReal α := by
  sorry

/-- **Bonferroni FWER control** (Lu-BDA §17). Rejecting `{ j : pⱼ ≤ α/N }` controls the
family-wise error rate: `FWER ≤ (N₀/N)·α ≤ α`. -/
theorem bonferroni_fwer_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for the union bound over events
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: null marginals super-uniform; Lu-BDA §17
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FWER H₀ (bonferroniRejects α p) μ ≤ ENNReal.ofReal ((H₀.card : ℝ) / N * α) := by
  sorry

end StatLean.MultipleTesting
