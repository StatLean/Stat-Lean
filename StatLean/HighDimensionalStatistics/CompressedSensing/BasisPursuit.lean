import StatLean.HighDimensionalStatistics.CompressedSensing.Defs
import StatLean.HighDimensionalStatistics.Lasso.Defs

/-!
# Basis pursuit — shared structural lemmas

The two lemmas that the cone theorem (`ConeTheorem.lean`, Lu §6 `thm:cone`) and the
RIP recovery theorem (`RIPRecovery.lean`, Lu §7 `thm:rip`) both rely on:

* `deviation_mem_cone_of_basisPursuit` — optimality of basis pursuit forces the error
  `Δ = β̂ − β*` into the cone `C(S) = reCone S 1` (book eq:cone-ineq).
* `unique_basisPursuit_of_cone_trivial` — if `C(S) ∩ Null(X) = {0}` then `β*` is the
  unique basis-pursuit solution (the sufficiency core, shared by both theorems).

Concept-layer (theorem-agnostic); the cone `C(S)` is `reCone S 1` from `Lasso/Defs.lean`.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Feasibility + ℓ¹-domination ⟹ cone membership** (Lu §6, eq:cone-ineq core). For
`β*` supported on `S`, any `β` with the same image (`X β = X β*`) and no larger ℓ¹ norm
has its deviation `β − β*` in the cone `C(S) = reCone S 1`. The shared engine of both
`deviation_mem_cone_of_basisPursuit` and the uniqueness clause of
`unique_basisPursuit_of_cone_trivial`. -/
private theorem mem_cone_of_feasible_of_le
    (S : Finset (Fin d))
    (βstar β : EuclideanSpace ℝ (Fin d))
    (hsupp : ∀ i ∉ S, βstar.ofLp i = 0)
    (hle : l1Norm β ≤ l1Norm βstar) :
    (β - βstar) ∈ reCone S 1 := by
  set Δ := β - βstar with hΔ
  have hβ : β = βstar + Δ := by rw [hΔ]; abel
  change l1Norm (restrict Sᶜ Δ) ≤ 1 * l1Norm (restrict S Δ)
  rw [one_mul]
  -- β* supported on S ⟹ its complement-restriction vanishes
  have hcompl : restrict Sᶜ βstar = 0 := restrict_compl_eq_zero S βstar hsupp
  -- ‖β*‖₁ = ‖β*|_S‖₁
  have e2 : l1Norm βstar = l1Norm (restrict S βstar) := by
    rw [l1Norm_split S βstar, hcompl]; simp
  -- split ‖β‖₁ and rewrite the two blocks
  have e3 : restrict S β = restrict S βstar + restrict S Δ := by
    rw [hβ]; exact restrict_add S βstar Δ
  have e4 : restrict Sᶜ β = restrict Sᶜ Δ := by
    rw [hβ, restrict_add, hcompl, zero_add]
  have hβval : l1Norm β
      = l1Norm (restrict S βstar + restrict S Δ) + l1Norm (restrict Sᶜ Δ) := by
    rw [l1Norm_split S β, e3, e4]
  have hle2 : l1Norm β ≤ l1Norm (restrict S βstar) := e2 ▸ hle
  have rt := l1Norm_sub_le (restrict S βstar) (restrict S Δ)
  linarith [hβval, hle2, rt]

/-- **Optimality ⟹ cone membership** (Lu §6, eq:cone-ineq). If `β*` is supported on
`S` and `β̂` is a basis-pursuit solution for `Y = X β*`, then the error `β̂ − β*`
lies in the cone `C(S) = reCone S 1`, i.e. `‖(β̂−β*)_{Sᶜ}‖₁ ≤ ‖(β̂−β*)_S‖₁`.

Proof (book): from feasibility `‖β̂‖₁ ≤ ‖β*‖₁`, split `‖·‖₁` over `S`/`Sᶜ`
(`l1Norm_split`), use `β*` supported on `S` and the reverse triangle inequality on the
`S`-block. -/
theorem deviation_mem_cone_of_basisPursuit
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (βstar βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β* is supported on S (β*ⱼ = 0 for j ∉ S); Lu-BDA §6 (thm:cone)
    (hsupp : ∀ i ∉ S, βstar.ofLp i = 0)
    -- USER-INPUT: β̂ is a basis-pursuit solution for Y = X β*; Lu-BDA §6 (thm:cone)
    (hbp : IsBasisPursuit X (designMap X βstar) βhat) :
    (βhat - βstar) ∈ reCone S 1 :=
  mem_cone_of_feasible_of_le S βstar βhat hsupp (hbp.2 βstar rfl)

/-- **Cone-condition ⟹ unique recovery** (Lu §6, sufficiency of `thm:cone`). If the
cone `C(S) = reCone S 1` meets the null space `Null(X) = ker (designMap X)` only at
`0`, then for any `β*` supported on `S` the basis-pursuit problem for `Y = X β*` has
`β*` as its unique solution.

Proof (book): any feasible competitor `β` with `‖β‖₁ ≤ ‖β*‖₁` has `Δ = β − β* ∈
Null(X)` (same image) and `Δ ∈ C(S)` (by `deviation_mem_cone_of_basisPursuit`), hence
`Δ ∈ C(S) ∩ Null(X) = {0}`, so `β = β*`. -/
theorem unique_basisPursuit_of_cone_trivial
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    -- USER-INPUT: cone ∩ null space is trivial, C(S) ∩ Null(X) = {0}; Lu-BDA §6 (eq:cone)
    (htriv : reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0})
    (βstar : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β* is supported on S; Lu-BDA §6 (thm:cone)
    (hsupp : ∀ i ∉ S, βstar.ofLp i = 0) :
    IsUniqueBasisPursuit X (designMap X βstar) βstar := by
  -- Uniqueness: any feasible competitor with no larger ℓ¹ norm equals β*.
  have uniq : ∀ β, designMap X β = designMap X βstar → l1Norm β ≤ l1Norm βstar →
      β = βstar := by
    intro β hfeas hle
    have hcone : (β - βstar) ∈ reCone S 1 :=
      mem_cone_of_feasible_of_le S βstar β hsupp hle
    have hker : (β - βstar) ∈
        (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hfeas, sub_self]
    have hmem : (β - βstar) ∈ ({0} : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [← htriv]; exact Set.mem_inter hcone hker
    exact sub_eq_zero.mp (Set.mem_singleton_iff.mp hmem)
  refine ⟨⟨rfl, ?_⟩, uniq⟩
  intro β hfeas
  by_cases hcase : l1Norm β ≤ l1Norm βstar
  · exact le_of_eq (congrArg l1Norm (uniq β hfeas hcase)).symm
  · exact (not_le.mp hcase).le

end StatLean.HighDimensionalStatistics
