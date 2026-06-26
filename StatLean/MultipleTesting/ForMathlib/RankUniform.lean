import Mathlib.Probability.Independence.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Exchangeability and rank uniformity — ForMathlib brick

The probabilistic core of conformal coverage (Candès, Lecture 9, §9.6): for an **exchangeable**,
almost-surely distinct family of real statistics `S₀, …, S_{m-1}`, the rank of any single `Sᵢ` is
uniform on `{1, …, m}`.

* `rankOf S i ω` — the rank `#{ j : Sⱼ(ω) ≤ Sᵢ(ω) }` of `Sᵢ` (1-indexed; `Sᵢ ≤ Sᵢ` always, so
  `rankOf ≥ 1`, and with distinct values `i ↦ rankOf S i ω` is a bijection onto `{1,…,m}`);
* `Exchangeable S μ` — the joint law of `(S₀,…,S_{m-1})` is invariant under permuting the indices
  (Mathlib v4.29.1 has **no** `Exchangeable`, so we define it);
* `measure_rankOf_le` — `μ{ rankOf S i ≤ k } = k/m` for `k ≤ m`.

In split-conformal prediction the calibration scores and the test score are exchangeable, so the
test score's rank is uniform — this is exactly what yields the `1−α` coverage guarantee
(`Conformal/Coverage.lean`). Theorem-agnostic.

Reference: Candès, Lecture 9, §9.6, STAT 300C Notes.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : ℕ}

/-- The rank of `Sᵢ` among `S₀, …, S_{m-1}`: `#{ j : Sⱼ(ω) ≤ Sᵢ(ω) }` (1-indexed). -/
def rankOf (S : Fin m → Ω → ℝ) (i : Fin m) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j => S j ω ≤ S i ω)).card

/-- `Exchangeable S μ`: the joint law of `(S₀,…,S_{m-1})` is invariant under index permutations —
`Measure.map (fun ω i => S (σ i) ω) μ = Measure.map (fun ω i => S i ω) μ` for every `σ`. -/
def Exchangeable (S : Fin m → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ σ : Equiv.Perm (Fin m),
    Measure.map (fun ω => (fun i => S (σ i) ω)) μ = Measure.map (fun ω => (fun i => S i ω)) μ

/-- **Rank uniformity** (Candès L9 §9.6, the exchangeability core of conformal coverage). For an
exchangeable, a.s. pairwise-distinct family `S₀,…,S_{m-1}`, the rank of any `Sᵢ` is uniform:
`μ{ rankOf S i ≤ k } = k/m` for `k ≤ m`. -/
theorem measure_rankOf_le (S : Fin m → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- USER-INPUT: each statistic is measurable; Candès L9 §9.6
    (hmeas : ∀ i, Measurable (S i))
    -- USER-INPUT: the family is exchangeable; Candès L9 §9.6
    (hExch : Exchangeable S μ)
    -- USER-INPUT: the statistics are a.s. pairwise distinct (continuous scores / tie-breaking);
    -- Candès L9 §9.6
    (hdistinct : ∀ᵐ ω ∂μ, Function.Injective (fun i => S i ω))
    (i : Fin m) {k : ℕ} (hk : k ≤ m) :
    μ {ω | rankOf S i ω ≤ k} = (k : ℝ≥0∞) / (m : ℝ≥0∞) := by
  sorry

end StatLean.MultipleTesting
