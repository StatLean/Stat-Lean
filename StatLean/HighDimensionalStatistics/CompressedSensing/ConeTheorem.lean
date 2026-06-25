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
  -- The restriction of `0` to any index set is `0` (used for `0 ∈ C(S)`).
  have hr0 : ∀ T : Finset (Fin d), restrict T (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
    intro T; apply WithLp.ofLp_injective 2; funext i
    rw [restrict_ofLp_apply]; simp
  apply subset_antisymm
  · -- `… ⊆ {0}`: a nonzero `v ∈ C(S) ∩ Null(X)` would give a feasible competitor.
    intro v hv
    obtain ⟨hcone, hker⟩ := hv
    have hc : l1Norm (restrict Sᶜ v) ≤ 1 * l1Norm (restrict S v) := hcone
    have hLv : designMap X v = 0 := by rwa [SetLike.mem_coe, LinearMap.mem_ker] at hker
    -- `β* = restrict S v` is supported on `S`.
    have hsupp : ∀ i ∉ S, (restrict S v).ofLp i = 0 := by
      intro i hi; rw [restrict_ofLp_apply, if_neg hi]
    -- Feasibility: `X (-v_{Sᶜ}) = X v_S`, since `X v = 0`.
    have hsum : designMap X (restrict S v) + designMap X (restrict Sᶜ v) = 0 := by
      rw [← map_add, restrict_add_restrict_compl]; exact hLv
    have key : designMap X (restrict S v) = - designMap X (restrict Sᶜ v) :=
      eq_neg_of_add_eq_zero_left hsum
    have hfeas : designMap X (-restrict Sᶜ v) = designMap X (restrict S v) := by
      rw [map_neg, ← key]
    -- ℓ¹-domination: `‖-v_{Sᶜ}‖₁ = ‖v_{Sᶜ}‖₁ ≤ ‖v_S‖₁`.
    have hle : l1Norm (-restrict Sᶜ v) ≤ l1Norm (restrict S v) := by
      rw [l1Norm_neg]; rw [one_mul] at hc; exact hc
    -- Uniqueness forces the competitor to equal `β*`.
    have heq : -restrict Sᶜ v = restrict S v :=
      (h (restrict S v) hsupp).2 (-restrict Sᶜ v) hfeas hle
    -- Hence `v = v_S + v_{Sᶜ} = -v_{Sᶜ} + v_{Sᶜ} = 0`.
    have hv0 : v = 0 := by
      have hvsum := restrict_add_restrict_compl S v
      rw [← heq, neg_add_cancel] at hvsum
      exact hvsum.symm
    rw [Set.mem_singleton_iff]; exact hv0
  · -- `{0} ⊆ …`: `0` is in the cone (both ℓ¹ sides vanish) and in the null space.
    intro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    refine ⟨?_, ?_⟩
    · change l1Norm (restrict Sᶜ (0 : EuclideanSpace ℝ (Fin d)))
        ≤ 1 * l1Norm (restrict S (0 : EuclideanSpace ℝ (Fin d)))
      rw [hr0, hr0]; simp
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_zero]

/-- **Cone theorem** (Lu, *Big Data Analysis* §6, `thm:cone`). Basis pursuit has `β*`
as its unique solution for every `β*` supported on `S` **iff** `C(S) ∩ Null(X) = {0}`. -/
theorem basisPursuit_unique_iff_cone_inter_ker
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ βstar : EuclideanSpace ℝ (Fin d), (∀ i ∉ S, βstar.ofLp i = 0) →
        IsUniqueBasisPursuit X (designMap X βstar) βstar)
    ↔ reCone S 1 ∩ (LinearMap.ker (designMap X) : Set (EuclideanSpace ℝ (Fin d))) = {0} :=
  ⟨fun h => cone_trivial_of_unique_basisPursuit X S h,
   fun htriv βstar hsupp => unique_basisPursuit_of_cone_trivial X S htriv βstar hsupp⟩

end StatLean.HighDimensionalStatistics
