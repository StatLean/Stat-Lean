import StatLean.HighDimensionalStatistics.CompressedSensing.BasisPursuit

/-!
# The cone theorem (Lu, *Big Data Analysis* §6, `thm:cone`)

**Theorem.** Basis pursuit recovers `β*` as its *unique* solution for every `β*`
supported on `S` **if and only if** the cone meets the null space trivially:
`C(S) ∩ Null(X) = {0}`, where `C(S) = reCone S 1 = {Δ : ‖Δ_{Sᶜ}‖₁ ≤ ‖Δ_S‖₁}` and
`Null(X) = ker (designMap X)`.

The sufficiency (`⟸`) is `unique_basisPursuit_of_cone_trivial` (`BasisPursuit.lean`).
The necessity (`⟹`) is `cone_trivial_of_unique_basisPursuit` below (book contrapositive:
a nonzero `v ∈ C(S) ∩ Null(X)` yields a feasible competitor to `restrict S v`).
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Necessity** of the cone condition (Lu §6, `thm:cone` ⟹). If basis pursuit
uniquely recovers every `β*` supported on `S`, then `C(S) ∩ Null(X) = {0}`.

Proof (book): suppose `0 ≠ v ∈ Null(X) ∩ C(S)`. Take `β* = restrict S v` (supported on
`S`) and the competitor `β = -restrict Sᶜ v`; then `X β = X β*` (since `X v = 0`) and
`‖β‖₁ = ‖v_{Sᶜ}‖₁ ≤ ‖v_S‖₁ = ‖β*‖₁` by `v ∈ C(S)`. Uniqueness forces `β = β*`,
i.e. `v = 0`, a contradiction. -/
theorem cone_trivial_of_unique_basisPursuit
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (h : ∀ βstar : EuclideanSpace ℝ (Fin d), (∀ i ∉ S, βstar.ofLp i = 0) →
        IsUniqueBasisPursuit X (designMap X βstar) βstar) :
    reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0} := by
  sorry

/-- **Cone theorem** (Lu, *Big Data Analysis* §6, `thm:cone`). Basis pursuit has `β*`
as its unique solution for every `β*` supported on `S` **iff** `C(S) ∩ Null(X) = {0}`. -/
theorem basisPursuit_unique_iff_cone_inter_ker
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ βstar : EuclideanSpace ℝ (Fin d), (∀ i ∉ S, βstar.ofLp i = 0) →
        IsUniqueBasisPursuit X (designMap X βstar) βstar)
    ↔ reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0} := by
  sorry

end StatLean.HighDimensionalStatistics
