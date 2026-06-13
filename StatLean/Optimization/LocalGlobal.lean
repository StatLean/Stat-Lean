import StatLean.Optimization.Convex.Defs
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Local minima are global minima (Proposition 10.1)

Lu, *Big Data Analysis* §10.2, Proposition `prop:local-global`:

* for a convex function, every local minimizer is a global minimizer;
* `x*` is a global minimizer iff `0 ∈ ∂f(x*)` (the first-order optimality
  condition for unconstrained problems).

The second statement is essentially definitional via `IsSubgradient`
(`0 ∈ ∂f x*` unfolds to `∀ y, 0 ≤ f y - f x*`); the first uses convexity.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lu-BDA Prop 10.1 (first-order optimality, unconstrained): `x*` is a global
minimizer of `f` iff `0 ∈ ∂f(x*)`. -/
theorem isGlobalMin_iff_zero_mem_subdifferential (f : E → ℝ) (xstar : E) :
    (∀ y, f xstar ≤ f y) ↔ (0 : E) ∈ subdifferential f xstar := by
  constructor
  · intro h y
    show ⟪(0 : E), y - xstar⟫_ℝ ≤ f y - f xstar
    rw [inner_zero_left]
    linarith [h y]
  · intro h y
    have hy : ⟪(0 : E), y - xstar⟫_ℝ ≤ f y - f xstar := h y
    rw [inner_zero_left] at hy
    linarith

/-- Lu-BDA Prop 10.1 (local minima are global minima): for convex `f`, any local
minimizer is a global minimizer. -/
theorem forall_le_of_isLocalMin
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {xstar : E}
    (hloc : IsLocalMin f xstar) (y : E) :
    f xstar ≤ f y := by
  by_contra hlt
  push_neg at hlt
  -- Reach the metric ε-form of the local-min property.
  have hloc_ev : ∀ᶠ z in 𝓝 xstar, f xstar ≤ f z := hloc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hloc_ev
  -- Pick `γ ∈ (0, 1]` with `γ * ‖y - xstar‖ < ε`.
  have hd_pos : 0 < ‖y - xstar‖ + 1 := by positivity
  have hε_d : 0 < ε / (‖y - xstar‖ + 1) := div_pos hε hd_pos
  set γ : ℝ := min 1 (ε / (‖y - xstar‖ + 1)) with hγ_def
  have hγ_pos : 0 < γ := lt_min one_pos hε_d
  have hγ_le1 : γ ≤ 1 := min_le_left _ _
  have hγ_le : γ ≤ ε / (‖y - xstar‖ + 1) := min_le_right _ _
  -- The convex-combination point `z = xstar + γ • (y - xstar) = (1-γ)•xstar + γ•y`.
  set z : E := xstar + γ • (y - xstar) with hz_def
  have hzx : z - xstar = γ • (y - xstar) := by rw [hz_def]; abel
  -- (1) `z` lies in the ε-ball around `xstar`, hence `f xstar ≤ f z`.
  have hdist : dist z xstar < ε := by
    rw [dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos hγ_pos]
    have h1 : γ * ‖y - xstar‖ ≤ ε / (‖y - xstar‖ + 1) * ‖y - xstar‖ :=
      mul_le_mul_of_nonneg_right hγ_le (norm_nonneg _)
    have h2 : ε / (‖y - xstar‖ + 1) * ‖y - xstar‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hd_pos]
      nlinarith [norm_nonneg (y - xstar)]
    linarith
  have hfz : f xstar ≤ f z := hball hdist
  -- (2) Convexity: `f z ≤ (1-γ) * f xstar + γ * f y`.
  have hz_alg : z = (1 - γ) • xstar + γ • y := by
    rw [hz_def, sub_smul, one_smul, smul_sub]; abel
  have hconv : f z ≤ (1 - γ) • f xstar + γ • f y := by
    rw [hz_alg]
    exact hf.2 (Set.mem_univ xstar) (Set.mem_univ y)
      (by linarith) hγ_pos.le (by ring)
  simp only [smul_eq_mul] at hconv
  -- (3) Combine: with `γ > 0` and `f y < f xstar`, we contradict `f xstar ≤ f z ≤ ...`.
  have hcomb : f xstar ≤ (1 - γ) * f xstar + γ * f y := le_trans hfz hconv
  nlinarith [hcomb, hlt, hγ_pos]

end StatLean.Optimization
