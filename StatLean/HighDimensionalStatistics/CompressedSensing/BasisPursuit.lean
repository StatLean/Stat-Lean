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
    (βhat - βstar) ∈ reCone S 1 := by
  sorry

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
  sorry

end StatLean.HighDimensionalStatistics
