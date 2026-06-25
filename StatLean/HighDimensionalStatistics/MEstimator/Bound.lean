import StatLean.HighDimensionalStatistics.MEstimator.Deviation
import StatLean.HighDimensionalStatistics.MEstimator.SubspaceLip

/-!
# Estimation-error bounds for general M-estimators (Wainwright Theorem 9.19, Corollary 9.20)

The central deterministic result of Chapter 9. Under restricted strong convexity (A1) and
decomposability (A2), conditioned on the good event, any optimum `θ̂` of the regularized
M-estimator (eq 9.3) satisfies the regularizer bound (9.48a) and the squared-error bound (9.48b).
Specializing to `θ* ∈ M` (so the approximation error vanishes) gives Corollary 9.20.

The proof goes through Lemma 9.21 (sign control): if the objective increment `ℱ` is strictly
positive on the sphere `{‖Δ‖ = δ} ∩ ℂ`, then `‖θ̂ − θ*‖ ≤ δ`, because `ℂ` is star-shaped, `ℱ` is
convex with `ℱ(0) = 0`, `ℱ(θ̂−θ*) ≤ 0`, and `θ̂−θ* ∈ ℂ` (Proposition 9.13).
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace
open StatLean.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 9.21** — sign control. If the objective increment `ℱ` (eq 9.31) is strictly positive on
the slice `𝕂(δ) = ℂ ∩ {‖Δ‖ = δ}`, then `‖θ̂ − θ*‖ ≤ δ`. Proof: contrapositive via star-shapedness of
`ℂ` about `0`, convexity of `ℱ`, `ℱ(0) = 0`, and `ℱ(θ̂−θ*) ≤ 0` (optimality), so a scaled copy
`t·(θ̂−θ*) ∈ 𝕂(δ)` would have `ℱ ≤ 0`, contradicting positivity. -/
theorem norm_error_le_of_pos_on_sphere (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex (A1); Wainwright §9.4.1.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam : ℝ)
    -- USER-INPUT: regularization weight `λ > 0`; Wainwright eq 9.3.
    (hlam : 0 < lam)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ Δ ∈ errorCone dr θstar, ‖Δ‖ = δ → 0 < Fcal L dr.Φ θstar lam Δ) :
    ‖θhat - θstar‖ ≤ δ := by
  sorry

/-- **Theorem 9.19(a)** — regularizer bound (eq 9.48a). Conditioned on the good event, any optimum
satisfies `Φ(θ̂ − θ*) ≤ 4·(Ψ(M̄)·‖θ̂ − θ*‖ + Φ(θ*_{Mᗮ}))`. Immediate from Proposition 9.13
(`θ̂−θ* ∈ ℂ`) + the subspace Lipschitz bound + non-expansiveness of the projection. No RSC needed. -/
theorem mestimator_reg_bound (dr : DecomposableReg E) (L : E → ℝ)
    (hL : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam : ℝ) (hlam : 0 < lam)
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam) :
    dr.Φ (θhat - θstar) ≤
      4 * (subspaceLip dr.Φ dr.Mbar * ‖θhat - θstar‖ + dr.Φ ((dr.M)ᗮ.starProjection θstar)) := by
  sorry

/-- **Theorem 9.19(b)** — squared-error bound (eq 9.48b). Under RSC `(κ, R, τ²)`, conditioned on the
good event, and provided `τ²·Ψ²(M̄) ≤ κ/64` and `εₙ² ≤ R²`, any optimum satisfies
`‖θ̂ − θ*‖² ≤ εₙ²(M̄, Mᗮ)`. Proof: the quadratic-form argument (eqs 9.50–9.53) shows `ℱ > 0` on the
sphere of radius `εₙ`, then Lemma 9.21 applies.

Book-constant note: the book states the slack condition as `τ²Ψ²(M̄) ≤ κ/64`; the provable constant
may differ by a small factor (to be documented in the proof). -/
theorem mestimator_l2_bound (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex (A1); Wainwright §9.4.1.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ R τSq : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R)
    -- USER-INPUT: restricted strong convexity `(κ, R, τ²)` (A1, Def 9.15); Wainwright eq 9.38.
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    -- USER-INPUT: curvature dominates tolerance·Lipschitz, `τ²Ψ²(M̄) ≤ κ/64`; Wainwright Thm 9.19(b).
    (hτ : τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2 ≤ κ / 64)
    -- USER-INPUT: `εₙ ≤ R` so the RSC ball contains the error; Wainwright Thm 9.19(b).
    (hεR : epsilonSq dr θstar lam κ τSq ≤ R ^ 2) :
    ‖θhat - θstar‖ ^ 2 ≤ epsilonSq dr θstar lam κ τSq := by
  sorry

/-- **Corollary 9.20**, eq (9.49b) — squared-error bound when `θ* ∈ M`. The approximation error
vanishes (`θ*_{Mᗮ} = 0`), so `‖θ̂ − θ*‖² ≤ 9(λ²/κ²)·Ψ²(M̄)`. -/
theorem cor_l2_bound_of_mem (dr : DecomposableReg E) (L : E → ℝ)
    (hL : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ R τSq : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R)
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    (hτ : τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2 ≤ κ / 64)
    (hεR : epsilonSq dr θstar lam κ τSq ≤ R ^ 2)
    -- USER-INPUT: target lies in the model subspace `θ* ∈ M`; Wainwright Cor 9.20.
    (hmem : θstar ∈ dr.M) :
    ‖θhat - θstar‖ ^ 2 ≤ 9 * (lam ^ 2 / κ ^ 2) * (subspaceLip dr.Φ dr.Mbar) ^ 2 := by
  sorry

/-- **Corollary 9.20**, eq (9.49a) — regularizer bound when `θ* ∈ M`:
`Φ(θ̂ − θ*) ≤ 6(λ/κ)·Ψ²(M̄)`. -/
theorem cor_reg_bound_of_mem (dr : DecomposableReg E) (L : E → ℝ)
    (hL : ConvexOn ℝ Set.univ L) (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ R τSq : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ) (hR : 0 < R)
    (hRSC : RSC L θstar dr.Φ κ R τSq)
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    (hτ : τSq * (subspaceLip dr.Φ dr.Mbar) ^ 2 ≤ κ / 64)
    (hεR : epsilonSq dr θstar lam κ τSq ≤ R ^ 2)
    (hmem : θstar ∈ dr.M) :
    dr.Φ (θhat - θstar) ≤ 6 * (lam / κ) * (subspaceLip dr.Φ dr.Mbar) ^ 2 := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
