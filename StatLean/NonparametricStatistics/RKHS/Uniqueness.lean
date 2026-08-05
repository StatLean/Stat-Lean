import StatLean.NonparametricStatistics.RKHS.Basic

/-!
# The kernel determines the RKHS

Two scalar RKHSs on the same set with the same reproducing kernel are "equal": there is a
(unique) isometric linear equivalence between them commuting with point evaluation.  In
particular they consist of the same functions on `X` with the same norms.  The proof
matches finite combinations of kernel functions (where the inner products are determined
by the kernel) and extends by density (`RKHS.kerFun_dense`).

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), Part I
§2, Théorème (uniqueness half of the Moore–Aronszajn correspondence).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
variable [RKHS 𝕜 H₁ X 𝕜] [RKHS 𝕜 H₂ X 𝕜]

/-- **The kernel determines the space**: two RKHSs on `X` with equal scalar kernels are
isometrically equivalent through an equivalence that commutes with point evaluation. -/
theorem exists_isometryEquiv_of_scalarKernel_eq
    -- USER-INPUT: the two spaces have the same reproducing kernel
    (hK : scalarKernel H₁ = scalarKernel (X := X) H₂) :
    ∃ e : H₁ ≃ₗᵢ[𝕜] H₂, ∀ (f : H₁) (x : X), (e f) x = f x := by
  sorry

/-- An evaluation-commuting map between RKHSs on `X` is unique (evaluations separate
points of an RKHS). -/
theorem evaluation_commuting_unique {e₁ e₂ : H₁ → H₂}
    (h₁ : ∀ (f : H₁) (x : X), (e₁ f) x = f x)
    (h₂ : ∀ (f : H₁) (x : X), (e₂ f) x = f x) : e₁ = e₂ := by
  sorry

/-- Two RKHSs with the same kernel consist of the same functions on `X`. -/
theorem range_coe_eq_of_scalarKernel_eq
    -- USER-INPUT: the two spaces have the same reproducing kernel
    (hK : scalarKernel H₁ = scalarKernel (X := X) H₂) :
    Set.range (fun f : H₁ => (f : X → 𝕜)) = Set.range (fun f : H₂ => (f : X → 𝕜)) := by
  sorry

end StatLean.NonparametricStatistics
