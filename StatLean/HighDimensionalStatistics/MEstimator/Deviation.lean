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
  -- Geometric decomposition: project `θ*` onto `(M, Mᗮ)` and `Δ` onto `(M̄, M̄ᗮ)`.
  set a := dr.M.starProjection θstar with ha_def
  set a' := (dr.M)ᗮ.starProjection θstar with ha'_def
  set b := dr.Mbar.starProjection Δ with hb_def
  set b' := (dr.Mbar)ᗮ.starProjection Δ with hb'_def
  have hθ : a + a' = θstar := dr.M.starProjection_add_starProjection_orthogonal θstar
  have hΔ : b + b' = Δ := dr.Mbar.starProjection_add_starProjection_orthogonal Δ
  have ha : a ∈ dr.M := dr.M.starProjection_apply_mem θstar
  have hb' : b' ∈ (dr.Mbar)ᗮ := (dr.Mbar)ᗮ.starProjection_apply_mem Δ
  -- `θ* + Δ = (a + b') + (a' + b)`; the reverse triangle inequality lower-bounds `Φ(θ*+Δ)`.
  have hsplit : θstar + Δ = (a + b') + (a' + b) := by rw [← hθ, ← hΔ]; abel
  have heq : (θstar + Δ) - (a' + b) = a + b' := by rw [hsplit]; abel
  have htri1 : dr.Φ (a + b') ≤ dr.Φ (θstar + Δ) + dr.Φ (a' + b) := by
    have h := map_sub_le_add dr.Φ (θstar + Δ) (a' + b)
    rwa [heq] at h
  have htri2 : dr.Φ (a' + b) ≤ dr.Φ a' + dr.Φ b := map_add_le_add dr.Φ a' b
  have hθle : dr.Φ θstar ≤ dr.Φ a + dr.Φ a' := by
    rw [← hθ]; exact map_add_le_add dr.Φ a a'
  -- Decomposability gives the matching equality on the `(M, M̄ᗮ)` cross term.
  have hdecomp : dr.Φ (a + b') = dr.Φ a + dr.Φ b' := dr.decomp a ha b' hb'
  linarith [htri1, htri2, hθle, hdecomp]

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
  set g := gradient L θstar with hg_def
  simp only [GoodEvent] at hG
  -- Convexity (first-order): `L(θ*+Δ) − L(θ*) ≥ ⟨∇L(θ*), Δ⟩`.
  have hgrad := inner_gradient_le_sub_of_convexOn hL hdiff θstar (θstar + Δ)
  rw [add_sub_cancel_left] at hgrad
  -- Hölder, both signs: `⟨g, Δ⟩ ≥ −Φ(Δ)·Φ*(g)`.
  have hh1 : ⟪Δ, g⟫_ℝ ≤ dr.Φ Δ * dr.Φstar g := dr.holder Δ g
  have hh2 : ⟪(-Δ), g⟫_ℝ ≤ dr.Φ (-Δ) * dr.Φstar g := dr.holder (-Δ) g
  rw [inner_neg_left, map_neg_eq_map] at hh2
  have hcomm : ⟪g, Δ⟫_ℝ = ⟪Δ, g⟫_ℝ := real_inner_comm Δ g
  have hlow : ⟪g, Δ⟫_ℝ ≥ -(dr.Φ Δ * dr.Φstar g) := by rw [hcomm]; linarith
  -- Good event + nonnegativity turn the Hölder bound into the `λ/2` bound.
  have hsnn : 0 ≤ dr.Φstar g := apply_nonneg dr.Φstar g
  have hpnn : 0 ≤ dr.Φ Δ := apply_nonneg dr.Φ Δ
  have hlamhalf_nn : 0 ≤ lam / 2 := le_trans hsnn hG
  have hmul1 : dr.Φ Δ * dr.Φstar g ≤ dr.Φ Δ * (lam / 2) :=
    mul_le_mul_of_nonneg_left hG hpnn
  -- `Φ(Δ) ≤ Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄})`.
  have hΔsplit : dr.Mbar.starProjection Δ + (dr.Mbar)ᗮ.starProjection Δ = Δ :=
    dr.Mbar.starProjection_add_starProjection_orthogonal Δ
  have hΔsum : dr.Φ Δ ≤
      dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) + dr.Φ (dr.Mbar.starProjection Δ) := by
    have h := map_add_le_add dr.Φ (dr.Mbar.starProjection Δ) ((dr.Mbar)ᗮ.starProjection Δ)
    rw [hΔsplit] at h
    linarith
  have hmul2 : dr.Φ Δ * (lam / 2) ≤
      (dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) + dr.Φ (dr.Mbar.starProjection Δ)) * (lam / 2) :=
    mul_le_mul_of_nonneg_right hΔsum hlamhalf_nn
  nlinarith [hgrad, hlow, hmul1, hmul2]

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
  set Δ := θhat - θstar with hΔdef
  have hθΔ : θstar + Δ = θhat := by rw [hΔdef]; abel
  -- Optimality `ℱ(Δ) ≤ 0`, rewritten at `θ̂ = θ* + Δ`.
  have hoptΔ : L (θstar + Δ) + lam * dr.Φ (θstar + Δ) ≤ L θstar + lam * dr.Φ θstar := by
    rw [hθΔ]; exact hopt θstar
  -- The two deviation bounds of Lemma 9.14.
  have hreg := reg_deviation_lower dr θstar Δ
  have hcost := cost_deviation_lower dr L hL hdiff θstar Δ lam hG
  -- Multiply the regularizer bound by `λ > 0` so it can combine linearly with optimality.
  have hlamreg := mul_le_mul_of_nonneg_left hreg (le_of_lt hlam)
  simp only [errorCone, Set.mem_setOf_eq]
  nlinarith [hoptΔ, hcost, hlamreg, hlam]

end StatLean.HighDimensionalStatistics.MEstimator
