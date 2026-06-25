import StatLean.HighDimensionalStatistics.MEstimator.Defs
import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms

/-!
# The ℓ₁/ℓ∞ decomposable regularizer instance (Wainwright Examples 9.1, 9.10; Table 9.1)

The concrete `DecomposableReg` used by the GLM corollaries: regularizer `Φ = ℓ₁`, dual norm
`Φ* = ℓ∞`, and model subspace `M = M̄ = M(S) = {θ : θⱼ = 0 for j ∉ S}` (vectors supported on `S`).
This packages: the ℓ₁ and ℓ∞ seminorm bundles, the ℓ₁/ℓ∞ Hölder pairing and its tightness
(sign-vector achievability), and ℓ₁-decomposability over `(M(S), M(S)ᗮ)` (disjoint supports).

Provided to `GLMCorollaries` as `l1DecomposableReg S`. With this instance, `Ψ(M(S)) = √s`,
the error cone is `reCone S 3`, and `Φ*(∇Lₙ(θ*)) = ‖∇Lₙ(θ*)‖∞`.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace

variable {d : ℕ}

/-- The **support submodule** `M(S) = {θ : θⱼ = 0 for all j ∉ S}` (Wainwright eq 9.23). -/
def suppSubmodule (S : Finset (Fin d)) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) where
  carrier := {θ | ∀ j ∉ S, θ.ofLp j = 0}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- ℓ₁ as a seminorm on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def l1Seminorm (d : ℕ) : Seminorm ℝ (EuclideanSpace ℝ (Fin d)) where
  toFun := l1Norm
  map_zero' := by sorry
  add_le' := by sorry
  neg' := by sorry
  smul' := by sorry

/-- ℓ∞ as a seminorm on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def linfSeminorm (d : ℕ) : Seminorm ℝ (EuclideanSpace ℝ (Fin d)) where
  toFun := linfNorm
  map_zero' := by sorry
  add_le' := by sorry
  neg' := by sorry
  smul' := by sorry

/-- ℓ₁/ℓ∞ **Hölder pairing**: `⟪u, v⟫ ≤ ‖u‖₁·‖v‖∞` (from `abs_inner_le_l1Norm_mul_linfNorm`). -/
lemma l1_linf_holder (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪u, v⟫_ℝ ≤ l1Norm u * linfNorm v := by
  sorry

/-- **ℓ∞ tightness** (the dual-norm variational characterization): if `⟪u, v⟫ ≤ c` for every `u` with
`‖u‖₁ ≤ 1`, then `‖v‖∞ ≤ c`. Proof: the coordinate sign vector `±eⱼ` (which has `‖·‖₁ = 1`) achieves
`⟪±eⱼ, v⟫ = |vⱼ|`, so `c ≥ |vⱼ|` for every `j`, hence `c ≥ ‖v‖∞`. -/
lemma linf_tight (v : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (h : ∀ u : EuclideanSpace ℝ (Fin d), l1Norm u ≤ 1 → ⟪u, v⟫_ℝ ≤ c) :
    linfNorm v ≤ c := by
  sorry

/-- `M(S)ᗮ = M(Sᶜ)`: the orthogonal complement of the `S`-supported subspace is the `Sᶜ`-supported one. -/
lemma suppSubmodule_orthogonal (S : Finset (Fin d)) :
    (suppSubmodule S)ᗮ = suppSubmodule Sᶜ := by
  sorry

/-- **ℓ₁-decomposability** (Wainwright Example 9.10): for `α` supported on `S` and `β` supported on
`Sᶜ` (disjoint supports), `‖α + β‖₁ = ‖α‖₁ + ‖β‖₁`. -/
lemma l1_decomp (S : Finset (Fin d)) (α : EuclideanSpace ℝ (Fin d)) (hα : α ∈ suppSubmodule S)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ∈ (suppSubmodule S)ᗮ) :
    l1Norm (α + β) = l1Norm α + l1Norm β := by
  sorry

/-- The **ℓ₁/ℓ∞ decomposable regularizer** with model subspace `M(S)` (`M = M̄`, the ideal case). -/
noncomputable def l1DecomposableReg (S : Finset (Fin d)) :
    DecomposableReg (EuclideanSpace ℝ (Fin d)) where
  M := suppSubmodule S
  Mbar := suppSubmodule S
  subset_Mbar := le_refl _
  Φ := l1Seminorm d
  Φstar := linfSeminorm d
  holder := l1_linf_holder
  tight := linf_tight
  decomp := l1_decomp S

end StatLean.HighDimensionalStatistics.MEstimator
