import StatLean.HighDimensionalStatistics.MEstimator.Defs

/-!
# Subspace Lipschitz constant — defining inequality (Wainwright Def 9.18)

The estimation-error theorems (Theorem 9.19, Corollary 9.20, Theorem 9.24) all use the defining
property of the subspace Lipschitz constant `Ψ(S) = sup_{u∈S∖0} Φ(u)/‖u‖`, namely
`Φ u ≤ Ψ(S)·‖u‖` for `u ∈ S` (this is step (iii) of eq 9.45). Establishing it requires the
`sSup` to be over a bounded-above set, which holds because any seminorm on a finite-dimensional
space is dominated by a multiple of the inner-product norm.

Concept-layer helper (theorem-agnostic); consumed by `Bound.lean` and `DualBound.lean`.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Finite-dimensional seminorm bound.** Any seminorm `Φ` on a finite-dimensional inner-product
space is dominated by a multiple of the norm: `∃ C ≥ 0, ∀ x, Φ x ≤ C·‖x‖`. Proof via an
orthonormal basis: `Φ x ≤ ∑ᵢ |⟨bᵢ,x⟩|·Φ(bᵢ) ≤ √(∑Φ(bᵢ)²)·‖x‖` (triangle + Cauchy–Schwarz). -/
lemma seminorm_le_const_mul_norm (Φ : Seminorm ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, Φ x ≤ C * ‖x‖ := by
  sorry

/-- The subspace Lipschitz constant is nonnegative (it is an `sSup` of nonnegative ratios, with the
empty/`S = 0` case giving `sSup ∅ = 0`). -/
lemma subspaceLip_nonneg (Φ : Seminorm ℝ E) (S : Submodule ℝ E) :
    0 ≤ subspaceLip Φ S := by
  sorry

/-- **Defining inequality of `Ψ(S)`** (Wainwright Def 9.18 / eq 9.45 step iii): for `u ∈ S`,
`Φ u ≤ Ψ(S)·‖u‖`. For `u = 0` both sides vanish; for `u ≠ 0`, `Φ(u)/‖u‖` is a member of the set
whose `sSup` is `Ψ(S)`, and that set is bounded above by `seminorm_le_const_mul_norm`. -/
lemma subspaceLip_le (Φ : Seminorm ℝ E) (S : Submodule ℝ E) {u : E} (hu : u ∈ S) :
    Φ u ≤ subspaceLip Φ S * ‖u‖ := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
