import StatLean.HighDimensionalStatistics.CompressedSensing.ConeTheorem
import StatLean.HighDimensionalStatistics.ForMathlib.TopK

/-!
# Perfect recovery under RIP (Lu, *Big Data Analysis* §7, `thm:rip`)

**Theorem.** If `X` is `3s`-RIP with constant `δ < 1/3`, then basis pursuit perfectly
recovers any `s`-sparse `β*`: the basis-pursuit problem for `Y = X β*` has `β*` as its
unique solution.

Proof (book): write `Δ = β̂ − β* ∈ Null(X)`. Optimality gives `Δ ∈ C(S)`
(`deviation_mem_cone_of_basisPursuit`). Shell `Δ_{Sᶜ}` into `2s`-blocks
(`orderedBlocks`, `TopK.lean`); applying `3s`-RIP to the head `S ∪ B₀` against the tail
blocks and bridging ℓ²↔ℓ¹ (`‖block_{j+1}‖₂ ≤ (1/√(2s))‖block_j‖₁`) yields the
contraction `‖Δ_S‖₁ ≤ √((1+δ)/(2(1−δ)))·‖Δ_{Sᶜ}‖₁` with ratio `< 1` exactly when
`δ < 1/3`. With the cone bound `‖Δ_{Sᶜ}‖₁ ≤ ‖Δ_S‖₁` this forces `Δ = 0`, hence `β̂ = β*`.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Perfect recovery under RIP** (Lu §7, `thm:rip`). `3s`-RIP with `δ < 1/3` implies
basis pursuit uniquely recovers every `s`-sparse `β*`.

`δ < 1/3` is the constant on the `3s`-RIP constant `δ_{3s}`; it is exactly the
threshold making the contraction ratio `√((1+δ)/(2(1−δ))) < 1`. -/
theorem basisPursuit_recovers_of_rip
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (δ : ℝ)
    -- USER-INPUT: 0 < δ; Lu-BDA §7 (thm:rip)
    (hδ0 : 0 < δ)
    -- USER-INPUT: δ < 1/3 (the 3s-RIP constant threshold); Lu-BDA §7 (thm:rip)
    (hδ : δ < 1 / 3)
    -- USER-INPUT: X satisfies the 3s-RIP with constant δ; Lu-BDA §7 (thm:rip)
    (hRIP : IsRIP X (3 * s) δ)
    (βstar : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β* is s-sparse; Lu-BDA §7 (thm:rip)
    (hsp : IsSparse s βstar) :
    IsUniqueBasisPursuit X (designMap X βstar) βstar := by
  sorry

end StatLean.HighDimensionalStatistics
