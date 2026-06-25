import StatLean.HighDimensionalStatistics.MEstimator.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# Deviation inequalities and error-cone membership (Wainwright Lemma 9.14, Proposition 9.13)

The first structural consequence of decomposability: on the good event `𝔾(λ)`, the error
`Δ̂ = θ̂ − θ*` of any optimum of the regularized M-estimator (eq 9.3) lies in the cone
`ℂ(M, M̄ᗮ)` (Proposition 9.13). The engine is the pair of deviation inequalities of Lemma 9.14:
a purely geometric lower bound on the regularizer increment (eq 9.32, from decomposability +
triangle inequality) and a convexity/Hölder lower bound on the cost increment (eq 9.33).

All `θ*` projection terms are onto `Mᗮ` (the model subspace `M`), as the decomposability step
`Φ(θ*_M + Δ_{M̄ᗮ}) = Φ(θ*_M) + Φ(Δ_{M̄ᗮ})` requires `θ*_M ∈ M`; the `Δ` projections are onto `M̄`/`M̄ᗮ`.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace
open StatLean.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 9.14, eq (9.32)** — regularizer deviation lower bound. For any decomposable regularizer
and any `θ*, Δ`,
`Φ(θ* + Δ) − Φ(θ*) ≥ Φ(Δ_{M̄ᗮ}) − Φ(Δ_{M̄}) − 2·Φ(θ*_{Mᗮ})`.
Geometric: decomposability (`dr.decomp`) applied to `θ*_M` and `Δ_{M̄ᗮ}`, plus the triangle
inequality. No convexity or good event needed. -/
theorem reg_deviation_lower (dr : DecomposableReg E) (θstar Δ : E) :
    dr.Φ (θstar + Δ) - dr.Φ θstar ≥
      dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) - dr.Φ (dr.Mbar.starProjection Δ)
        - 2 * dr.Φ ((dr.M)ᗮ.starProjection θstar) := by
  sorry

/-- **Lemma 9.14, eq (9.33)** — cost deviation lower bound. For a convex differentiable cost `L`,
conditioned on the good event `Φ*(∇L(θ*)) ≤ λ/2`,
`L(θ* + Δ) − L(θ*) ≥ −(λ/2)·(Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄}))`.
Proof: convexity gives `L(θ*+Δ) − L(θ*) ≥ ⟨∇L(θ*), Δ⟩ ≥ −Φ*(∇L(θ*))·Φ(Δ) ≥ −(λ/2)Φ(Δ)`, then
`Φ(Δ) ≤ Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄})`. -/
theorem cost_deviation_lower (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` is convex (A1); Wainwright §9.4.1 (A1).
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` is differentiable; Wainwright §9.3 (gradient/score well-defined).
    (hdiff : Differentiable ℝ L)
    (θstar Δ : E) (lam : ℝ)
    -- USER-INPUT: good event `𝔾(λ) = {Φ*(∇L(θ*)) ≤ λ/2}`; Wainwright eq 9.28/9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam) :
    L (θstar + Δ) - L θstar ≥
      -(lam / 2) * (dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) + dr.Φ (dr.Mbar.starProjection Δ)) := by
  sorry

/-- **Proposition 9.13** — error-cone membership. For a convex differentiable cost `L`, a decomposable
regularizer, and any optimum `θ̂` of `L + λ·Φ` (`λ > 0`), conditioned on the good event the error
`θ̂ − θ*` lies in the cone `ℂ(M, M̄ᗮ)` (eq 9.29). Immediate from Lemma 9.14: combining (9.32)+(9.33)
with `ℱ(θ̂−θ*) ≤ 0` (optimality) gives `Φ(Δ̂_{M̄ᗮ}) ≤ 3Φ(Δ̂_{M̄}) + 4Φ(θ*_{Mᗮ})`. -/
theorem error_mem_cone (dr : DecomposableReg E) (L : E → ℝ)
    -- USER-INPUT: cost `L` is convex (A1); Wainwright §9.4.1 (A1).
    (hL : ConvexOn ℝ Set.univ L)
    -- USER-INPUT: cost `L` is differentiable; Wainwright §9.3.
    (hdiff : Differentiable ℝ L)
    (θstar θhat : E) (lam : ℝ)
    -- USER-INPUT: regularization weight `λ > 0`; Wainwright eq 9.3.
    (hlam : 0 < lam)
    -- USER-INPUT: `θ̂` minimizes the regularized objective `L + λ·Φ` (the M-estimator); Wainwright eq 9.3.
    (hopt : ∀ θ, L θhat + lam * dr.Φ θhat ≤ L θ + lam * dr.Φ θ)
    -- USER-INPUT: good event `𝔾(λ)`; Wainwright eq 9.28/9.46.
    (hG : GoodEvent dr.Φstar (gradient L θstar) lam) :
    (θhat - θstar) ∈ errorCone dr θstar := by
  sorry

end StatLean.HighDimensionalStatistics.MEstimator
