import StatLean.HighDimensionalStatistics.MEstimator.Deviation
import StatLean.HighDimensionalStatistics.MEstimator.SubspaceLip
import StatLean.Optimization.Convex.Subgradient

/-!
# Dual-norm (`Φ*`) error bound for general M-estimators (Wainwright Theorem 9.24, Lemma 9.25)

The second, sharper error guarantee of Chapter 9: under the `Φ*`-norm curvature condition
(Definition 9.22) instead of RSC, the error is controlled in the dual norm,
`Φ*(θ̂ − θ*) ≤ 3λ/κ` (Theorem 9.24). For `ℓ₁`-regularization this is an `ℓ∞` bound, stronger than
the `ℓ₂`/`ℓ₁` bounds of Theorem 9.19.

Two ingredients beyond the deterministic machinery of `Bound.lean`:
* the **stationarity** of the composite minimizer `θ̂` — there is a subgradient `z ∈ ∂Φ(θ̂)` with
  `∇L(θ̂) + λ·z = 0`. Mathlib has no subdifferential calculus, so this is hand-built from optimality
  via a directional-derivative argument (`exists_stationary_subgradient`);
* **Lemma 9.25**, `Φ(Δ) ≤ 16·Ψ²(M̄)·Φ*(Δ)` on the cone when `θ* ∈ M` (eq 9.60).
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace
open StatLean.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Stationarity of the composite minimizer.** If `θ̂` minimizes `L + λ·Φ` with `L` convex
differentiable, `Φ` a (convex) seminorm and `λ > 0`, then there is a subgradient `z ∈ ∂Φ(θ̂)` with
`∇L(θ̂) + λ·z = 0` — i.e. `−∇L(θ̂)/λ ∈ ∂Φ(θ̂)`. Mathlib has no convex subdifferential sum rule, so
this is proved by hand: for each direction `w`, the one-sided derivative of `t ↦ L(θ̂+tw)+λΦ(θ̂+tw)`
at `0` is `≥ 0`, giving `⟨−∇L(θ̂), w⟩ ≤ λ(Φ(θ̂+w) − Φ(θ̂))`. -/
theorem exists_stationary_subgradient (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex; Wainwright §9.4.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θhat : E) (lam : ℝ)
    -- USER-INPUT: `λ > 0`; Wainwright eq 9.3.
    (hlam : 0 < lam)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ) :
    ∃ z : E, IsSubgradient (fun x => dr.Φ x) θhat z ∧ gradient L θhat + lam • z = 0 := by
  sorry

/-- **Lemma 9.25** (eq 9.60). When `θ* ∈ M`, for any `Δ ∈ ℂ(M, M̄ᗮ)` we have
`Φ(Δ) ≤ 16·Ψ²(M̄)·Φ*(Δ)`. Proof: eq 9.45 gives `Φ(Δ) ≤ 4Ψ(M̄)‖Δ‖`; Hölder gives
`‖Δ‖² ≤ Φ(Δ)·Φ*(Δ) ≤ 4Ψ(M̄)‖Δ‖·Φ*(Δ)`, hence `‖Δ‖ ≤ 4Ψ(M̄)Φ*(Δ)`; combine. -/
theorem reg_le_dual_of_mem (dr : DecomposableReg E) (θstar : E)
    -- USER-INPUT: target lies in the model subspace `θ* ∈ M`; Wainwright Lemma 9.25.
    (hmem : θstar ∈ dr.M) (Δ : E) (hΔ : Δ ∈ errorCone dr θstar) :
    dr.Φ Δ ≤ 16 * (subspaceLip dr.Φ dr.Mbar) ^ 2 * dr.Φstar Δ := by
  sorry

/-- **Theorem 9.24** — dual-norm error bound (eq 9.58). Given `θ* ∈ M`, the `Φ*`-curvature condition
(A1′, Def 9.22) with `(κ, τ; R)`, decomposability (A2), and `τ·Ψ²(M̄) < κ/32`, then conditioned on the
good event `𝔾(λ)` and `Φ*(θ̂−θ*) ≤ R`, any optimum satisfies `Φ*(θ̂ − θ*) ≤ 3λ/κ`.

Proof: stationarity gives `∇L(θ̂) = −λz`, `Φ*(z) ≤ 1`; with the good event,
`Φ*(∇L(θ̂)−∇L(θ*)) ≤ 3λ/2`. The curvature condition + Lemma 9.25 turn this into
`(κ − 16τΨ²(M̄))·Φ*(θ̂−θ*) ≤ 3λ/2`, and `τΨ²(M̄) < κ/32` finishes. -/
theorem mestimator_dual_bound (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` convex (A1′ context); Wainwright §9.4.2.
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam κ τ R : ℝ)
    (hlam : 0 < lam) (hκ : 0 < κ)
    -- USER-INPUT: target lies in the model subspace `θ* ∈ M`; Wainwright Thm 9.24.
    (hmem : θstar ∈ dr.M)
    -- USER-INPUT: `Φ*`-curvature condition `(κ, τ; R)` (A1′, Def 9.22); Wainwright eq 9.55.
    (hcurv : dualCurvature L θstar dr.Φ dr.Φstar κ τ R)
    -- USER-INPUT: `θ̂` minimizes `L + λ·Φ`; Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam)
    -- USER-INPUT: slack condition `τ·Ψ²(M̄) < κ/32`; Wainwright Thm 9.24.
    (hτ : τ * (subspaceLip dr.Φ dr.Mbar) ^ 2 < κ / 32)
    -- USER-INPUT: localization `Φ*(θ̂−θ*) ≤ R` (the conditioning event); Wainwright Thm 9.24.
    (hRloc : dr.Φstar (θhat - θstar) ≤ R) :
    dr.Φstar (θhat - θstar) ≤ 3 * lam / κ := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
