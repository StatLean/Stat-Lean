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
  let b := stdOrthonormalBasis ℝ E
  refine ⟨∑ i, Φ (b i), Finset.sum_nonneg (fun i _ => apply_nonneg Φ (b i)), fun x => ?_⟩
  calc Φ x = Φ (∑ i, b.repr x i • b i) := by rw [b.sum_repr x]
    _ ≤ ∑ i, Φ (b.repr x i • b i) :=
        Finset.le_sum_of_subadditive Φ (by simp) (fun a c => map_add_le_add Φ a c) _ _
    _ = ∑ i, |b.repr x i| * Φ (b i) := by simp_rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖x‖ * Φ (b i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg Φ (b i))
        rw [b.repr_apply_apply x i]
        calc |⟪b i, x⟫_ℝ| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm (b i) x
          _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]
    _ = (∑ i, Φ (b i)) * ‖x‖ := by rw [Finset.sum_mul]; simp_rw [mul_comm]

/-- The subspace Lipschitz constant is nonnegative (it is an `sSup` of nonnegative ratios, with the
empty/`S = 0` case giving `sSup ∅ = 0`). -/
lemma subspaceLip_nonneg (Φ : Seminorm ℝ E) (S : Submodule ℝ E) :
    0 ≤ subspaceLip Φ S := by
  unfold subspaceLip
  apply Real.sSup_nonneg
  rintro y ⟨u, -, rfl⟩
  exact div_nonneg (apply_nonneg Φ u) (norm_nonneg u)

/-- **Defining inequality of `Ψ(S)`** (Wainwright Def 9.18 / eq 9.45 step iii): for `u ∈ S`,
`Φ u ≤ Ψ(S)·‖u‖`. For `u = 0` both sides vanish; for `u ≠ 0`, `Φ(u)/‖u‖` is a member of the set
whose `sSup` is `Ψ(S)`, and that set is bounded above by `seminorm_le_const_mul_norm`. -/
lemma subspaceLip_le (Φ : Seminorm ℝ E) (S : Submodule ℝ E) {u : E} (hu : u ∈ S) :
    Φ u ≤ subspaceLip Φ S * ‖u‖ := by
  by_cases hu0 : u = 0
  · simp [hu0, map_zero]
  · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    rw [← div_le_iff₀ hnorm]
    unfold subspaceLip
    apply le_csSup
    · obtain ⟨C, hC0, hC⟩ := seminorm_le_const_mul_norm Φ
      refine ⟨C, ?_⟩
      rintro y ⟨v, ⟨_, hv0⟩, rfl⟩
      have hvn : 0 < ‖v‖ := norm_pos_iff.mpr (by simpa using hv0)
      rw [div_le_iff₀ hvn]
      exact hC v
    · exact ⟨u, ⟨hu, hu0⟩, rfl⟩

end StatLean.HighDimensionalStatistics.MEstimator
