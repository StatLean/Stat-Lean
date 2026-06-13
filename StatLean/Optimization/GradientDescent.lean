import StatLean.Optimization.Smoothness.CoCoercive
import StatLean.Optimization.ForMathlib.FirstOrderConvex
import StatLean.Optimization.ForMathlib.GradientCalc

/-!
# Convergence of gradient descent (Theorem 11.1)

Lu, *Big Data Analysis* §11.1, Theorem `thm:gd`: for a convex `L`-smooth `f`,
the gradient-descent iterates `x_{t+1} = x_t - (1/L) ∇f(x_t)` satisfy an
`O(1/t)` rate `f(x_t) - f(x*) ≤ C · ‖x_0 - x*‖² / t`.

The iteration is supplied abstractly: `x : ℕ → E` with the recurrence `hrec`,
and `x*` is a global minimizer (`hmin`), from which `∇f(x*) = 0` is derived
(`gradient_eq_zero_of_forall_le`). The proof goes through co-coercivity
(`cocoercive`, Lemma 11.1): the distance `‖x_t - x*‖` is non-increasing, and a
telescoping/recursive bound on `δ_t = f(x_t) - f(x*)` yields the rate.

**Constant.** The book writes `2L‖x_0 - x*‖²/t`. The constant `2L` is in fact
**looser** than what our telescoping proves: setting `ω := 1/(2L‖x_0-x*‖²)`,
the recursion `δ_{t+1} ≤ δ_t - ω δ_t²` together with `δ_0 ≥ 0` gives
`1/δ_t ≥ ω t`, hence `δ_t ≤ 1/(ω t) = 2L‖x_0 - x*‖² / t`. We therefore keep
the book constant `2L`; the bound stated here matches the book exactly.

## Proof outline

* `gd_descent_step` — smoothness at consecutive iterates gives
  `f(x_{t+1}) ≤ f(x_t) - (1/(2L))‖∇f(x_t)‖²`.
* `gd_distance_step` / `gd_distance_bound` — co-coercivity at `(x_t, x*)`
  with `∇f(x*) = 0` gives `‖x_{t+1} - x*‖² ≤ ‖x_t - x*‖²`, and by induction
  `‖x_t - x*‖² ≤ ‖x_0 - x*‖²`.
* `gd_gap_quad_bound` — convexity + Cauchy–Schwarz + distance bound give
  `(f(x_t) - f(x*))² ≤ ‖∇f(x_t)‖² · ‖x_0 - x*‖²`.
* `gd_iterate_eq_xstar_of_start` — handles the degenerate case `x_0 = x*`.
* `gd_inv_gap_bound` — telescoping induction on the recursive bound
  `δ_{t+1} ≤ δ_t - ω δ_t²`.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Step 1 (descent inequality).** One step of gradient descent with step
`1/L` on an `L`-smooth function decreases `f` by at least `(1/(2L))‖∇f‖²`.
Proof: substitute the recurrence `x_{t+1} - x_t = -(1/L) ∇f(x_t)` into the
`L`-smoothness upper bound `f y ≤ f x + ⟪∇f x, y - x⟫ + (L/2)‖x - y‖²` and
simplify `-(1/L) + (L/2)(1/L)² = -1/(2L)`. -/
private lemma gd_descent_step
    {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    {x : ℕ → E} (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    (t : ℕ) :
    f (x (t + 1)) ≤ f (x t) - (1 / (2 * L)) * ‖gradient f (x t)‖ ^ 2 := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hL_inv_pos : (0 : ℝ) < 1 / L := by positivity
  have hsm := hsmooth (x t) (x (t + 1))
  have hxt1_sub : x (t + 1) - x t = -((1 / L) • gradient f (x t)) := by
    rw [hrec t]; abel
  have hxt_sub : x t - x (t + 1) = (1 / L) • gradient f (x t) := by
    rw [hrec t]; abel
  have h_inner : ⟪gradient f (x t), x (t + 1) - x t⟫_ℝ
      = -((1 / L) * ‖gradient f (x t)‖ ^ 2) := by
    rw [hxt1_sub, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have h_norm_sq : ‖x t - x (t + 1)‖ ^ 2 = (1 / L) ^ 2 * ‖gradient f (x t)‖ ^ 2 := by
    rw [hxt_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hL_inv_pos]
    ring
  rw [h_inner, h_norm_sq] at hsm
  have h_coef : f (x t) + -((1 / L) * ‖gradient f (x t)‖ ^ 2)
        + (L / 2) * ((1 / L) ^ 2 * ‖gradient f (x t)‖ ^ 2)
      = f (x t) - (1 / (2 * L)) * ‖gradient f (x t)‖ ^ 2 := by
    field_simp
    ring
  linarith [hsm, h_coef]

/-- **Step 2 (distance non-increasing).** One step of gradient descent with
step `1/L` does not increase the distance to a global minimizer.
Proof: expand `‖(x_t - x*) - (1/L)∇f(x_t)‖²` and use co-coercivity at
`(x_t, x*)` with `∇f(x*) = 0`. -/
private lemma gd_distance_step
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    {x : ℕ → E} (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y) (t : ℕ) :
    ‖x (t + 1) - xstar‖ ^ 2 ≤ ‖x t - xstar‖ ^ 2 := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hL_inv_pos : (0 : ℝ) < 1 / L := by positivity
  have hgrad_xstar : gradient f xstar = 0 := gradient_eq_zero_of_forall_le hdiff hmin
  have h_eq : x (t + 1) - xstar = (x t - xstar) - (1 / L) • gradient f (x t) := by
    rw [hrec t]; abel
  -- Expand ‖(x_t - x*) - (1/L)∇f(x_t)‖².
  have h_expand : ‖x (t + 1) - xstar‖ ^ 2
      = ‖x t - xstar‖ ^ 2
        - 2 * ⟪x t - xstar, (1 / L) • gradient f (x t)⟫_ℝ
        + ‖(1 / L) • gradient f (x t)‖ ^ 2 := by
    rw [h_eq, norm_sub_sq_real]
  have h_inner_smul :
      ⟪x t - xstar, (1 / L) • gradient f (x t)⟫_ℝ
        = (1 / L) * ⟪x t - xstar, gradient f (x t)⟫_ℝ := by
    rw [real_inner_smul_right]
  have h_norm_smul :
      ‖(1 / L) • gradient f (x t)‖ ^ 2 = (1 / L) ^ 2 * ‖gradient f (x t)‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL_inv_pos]; ring
  -- Co-coercivity at (x_t, x*); ∇f(x*) = 0.
  have h_co := inner_gradient_sub_nonneg hf hdiff hL hsmooth (x t) xstar
  rw [hgrad_xstar] at h_co
  simp only [sub_zero] at h_co
  -- h_co : (1/(2L))‖∇f(x_t)‖² ≤ ⟪∇f(x_t), x_t - x*⟫_ℝ
  -- Real inner product is symmetric.
  have h_sym :
      ⟪gradient f (x t), x t - xstar⟫_ℝ = ⟪x t - xstar, gradient f (x t)⟫_ℝ :=
    real_inner_comm (x t - xstar) (gradient f (x t))
  rw [h_sym] at h_co
  rw [h_expand, h_inner_smul, h_norm_smul]
  -- Need: (1/L)²‖∇f‖² ≤ 2(1/L)⟪x_t - x*, ∇f(x_t)⟫_ℝ.
  -- From h_co (* 2/L > 0): (1/L²)‖∇f‖² ≤ (2/L)⟪⟫.
  have h_key : (1 / L) ^ 2 * ‖gradient f (x t)‖ ^ 2
      = (2 / L) * ((1 / (2 * L)) * ‖gradient f (x t)‖ ^ 2) := by
    field_simp
  have h_2L_nonneg : (0 : ℝ) ≤ 2 / L := by positivity
  have h_scaled : (2 / L) * ((1 / (2 * L)) * ‖gradient f (x t)‖ ^ 2)
      ≤ (2 / L) * ⟪x t - xstar, gradient f (x t)⟫_ℝ :=
    mul_le_mul_of_nonneg_left h_co h_2L_nonneg
  have h_rel : (2 / L) * ⟪x t - xstar, gradient f (x t)⟫_ℝ
      = 2 * ((1 / L) * ⟪x t - xstar, gradient f (x t)⟫_ℝ) := by ring
  linarith [h_scaled, h_key, h_rel]

/-- **Distance bound** (induction over Step 2): `‖x_t - x*‖² ≤ ‖x_0 - x*‖²`. -/
private lemma gd_distance_bound
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    {x : ℕ → E} (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y) (t : ℕ) :
    ‖x t - xstar‖ ^ 2 ≤ ‖x 0 - xstar‖ ^ 2 := by
  induction t with
  | zero => exact le_refl _
  | succ k ih =>
    have h := gd_distance_step hf hdiff hL hsmooth hrec hmin k
    linarith

/-- **Step 3 (quadratic gap bound).** Convexity + Cauchy–Schwarz + the
distance bound give `(f(x_t) - f(x*))² ≤ ‖∇f(x_t)‖² · ‖x_0 - x*‖²`. -/
private lemma gd_gap_quad_bound
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    {x : ℕ → E} (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y) (t : ℕ) :
    (f (x t) - f xstar) ^ 2 ≤ ‖gradient f (x t)‖ ^ 2 * ‖x 0 - xstar‖ ^ 2 := by
  -- Convexity at (x_t, x*): f(x_t) + ⟪∇f(x_t), x* - x_t⟫ ≤ f(x*).
  have h_conv : f (x t) + ⟪gradient f (x t), xstar - x t⟫_ℝ ≤ f xstar :=
    inner_gradient_le_sub_of_convexOn hf hdiff (x t) xstar
  have h_inner_neg :
      ⟪gradient f (x t), xstar - x t⟫_ℝ = -⟪gradient f (x t), x t - xstar⟫_ℝ := by
    rw [← inner_neg_right]; congr 1; abel
  have h_delta : f (x t) - f xstar ≤ ⟪gradient f (x t), x t - xstar⟫_ℝ := by
    linarith [h_conv, h_inner_neg]
  have h_delta_nonneg : 0 ≤ f (x t) - f xstar := by linarith [hmin (x t)]
  -- Square the convexity bound, using δ ≥ 0.
  have h_delta_sq :
      (f (x t) - f xstar) ^ 2 ≤ ⟪gradient f (x t), x t - xstar⟫_ℝ ^ 2 := by
    nlinarith [h_delta, h_delta_nonneg]
  -- Cauchy–Schwarz in real inner-product space.
  have h_CS :
      ⟪gradient f (x t), x t - xstar⟫_ℝ ^ 2
        ≤ ‖gradient f (x t)‖ ^ 2 * ‖x t - xstar‖ ^ 2 := by
    have h := real_inner_mul_inner_self_le (gradient f (x t)) (x t - xstar)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [h]
  have h_dist := gd_distance_bound hf hdiff hL hsmooth hrec hmin t
  have h_grad_sq_nonneg : 0 ≤ ‖gradient f (x t)‖ ^ 2 := sq_nonneg _
  calc (f (x t) - f xstar) ^ 2
      ≤ ⟪gradient f (x t), x t - xstar⟫_ℝ ^ 2 := h_delta_sq
    _ ≤ ‖gradient f (x t)‖ ^ 2 * ‖x t - xstar‖ ^ 2 := h_CS
    _ ≤ ‖gradient f (x t)‖ ^ 2 * ‖x 0 - xstar‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h_dist h_grad_sq_nonneg

/-- **Degenerate case.** If the iterate starts at the minimizer, it stays there. -/
private lemma gd_iterate_eq_xstar_of_start
    {f : E → ℝ} (hdiff : Differentiable ℝ f)
    {L : ℝ}
    {x : ℕ → E} (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y) (h0 : x 0 = xstar) (t : ℕ) :
    x t = xstar := by
  induction t with
  | zero => exact h0
  | succ k ih =>
    rw [hrec k, ih, gradient_eq_zero_of_forall_le hdiff hmin, smul_zero, sub_zero]

/-- **Step 4 (inverse-gap bound).** In the non-degenerate case `‖x_0 - x*‖² > 0`,
with `ω := 1/(2L‖x_0 - x*‖²)`, either `f(x_t) = f(x*)` (the iterate has
already converged in objective value) or `ω · t ≤ 1/(f(x_t) - f(x*))`.

Proof: induction on `t`. The recursion `δ_{t+1} ≤ δ_t - ω δ_t²` (from Steps 1
and 3) factors as `δ_t (1 - ω δ_t)`. While both factors are positive, taking
reciprocals and using `1/(1-x) ≥ 1 + x` for `x ∈ [0,1)` gives
`1/δ_{t+1} ≥ 1/δ_t + ω`, which telescopes to `1/δ_t ≥ ω t` (absorbing
`1/δ_0 ≥ 0`). -/
private lemma gd_inv_gap_bound
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    {x : ℕ → E} (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y)
    (hD : 0 < ‖x 0 - xstar‖ ^ 2) (t : ℕ) :
    f (x t) - f xstar = 0 ∨
      (0 < f (x t) - f xstar ∧
        (1 / (2 * L * ‖x 0 - xstar‖ ^ 2)) * (t : ℝ) ≤ 1 / (f (x t) - f xstar)) := by
  set ω : ℝ := 1 / (2 * L * ‖x 0 - xstar‖ ^ 2) with hω_def
  have hω_pos : 0 < ω := by rw [hω_def]; positivity
  induction t with
  | zero =>
    have hδ_nonneg : 0 ≤ f (x 0) - f xstar := by linarith [hmin (x 0)]
    rcases eq_or_lt_of_le hδ_nonneg with h | h
    · left; linarith
    · right
      refine ⟨h, ?_⟩
      rw [Nat.cast_zero, mul_zero]
      exact (one_div_pos.mpr h).le
  | succ k ih =>
    have hδk_nonneg : 0 ≤ f (x k) - f xstar := by linarith [hmin (x k)]
    have hδk1_nonneg : 0 ≤ f (x (k + 1)) - f xstar := by linarith [hmin (x (k + 1))]
    have h_descent := gd_descent_step hL hsmooth hrec k
    have h_quad := gd_gap_quad_bound hf hdiff hL hsmooth hrec hmin k
    -- Combine descent + quadratic gap to a recursion in δ alone.
    have h_recursive :
        f (x (k + 1)) - f xstar ≤ (f (x k) - f xstar) - ω * (f (x k) - f xstar) ^ 2 := by
      -- ω δ_k² ≤ (1/(2L)) ‖∇f(x_k)‖² (using δ² ≤ ‖∇f‖² D² and D² > 0).
      have h_step : ω * (f (x k) - f xstar) ^ 2
          ≤ (1 / (2 * L)) * ‖gradient f (x k)‖ ^ 2 := by
        rw [hω_def, div_mul_eq_mul_div, one_mul,
          div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L * ‖x 0 - xstar‖ ^ 2)]
        have hrw : (1 / (2 * L)) * ‖gradient f (x k)‖ ^ 2 * (2 * L * ‖x 0 - xstar‖ ^ 2)
              = ‖gradient f (x k)‖ ^ 2 * ‖x 0 - xstar‖ ^ 2 := by
          field_simp
        rw [hrw]
        exact h_quad
      linarith [h_descent, h_step]
    rcases ih with hk_zero | ⟨hk_pos, h_inv⟩
    · -- δ_k = 0 forces δ_{k+1} = 0.
      left
      have h_drop : f (x (k + 1)) - f xstar ≤ 0 := by
        rw [hk_zero] at h_recursive
        simpa using h_recursive
      linarith [hδk1_nonneg, h_drop]
    · -- δ_k > 0 and ω k ≤ 1/δ_k.
      by_cases hk1 : 0 < f (x (k + 1)) - f xstar
      · right
        refine ⟨hk1, ?_⟩
        -- Factor δ_k - ω δ_k² = δ_k (1 - ω δ_k); deduce 1 - ω δ_k > 0.
        have h_factored :
            f (x (k + 1)) - f xstar
              ≤ (f (x k) - f xstar) * (1 - ω * (f (x k) - f xstar)) := by
          have hfac :
              (f (x k) - f xstar) - ω * (f (x k) - f xstar) ^ 2
              = (f (x k) - f xstar) * (1 - ω * (f (x k) - f xstar)) := by ring
          linarith [h_recursive, hfac]
        have h_one_minus_pos : 0 < 1 - ω * (f (x k) - f xstar) := by
          by_contra h_neg
          push_neg at h_neg
          have h_prod_nonpos :
              (f (x k) - f xstar) * (1 - ω * (f (x k) - f xstar)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hk_pos.le h_neg
          linarith [h_factored, h_prod_nonpos, hk1]
        -- 1/δ_{k+1} ≥ 1/(δ_k (1 - ω δ_k)).
        have h_inv_step :
            1 / ((f (x k) - f xstar) * (1 - ω * (f (x k) - f xstar)))
              ≤ 1 / (f (x (k + 1)) - f xstar) :=
          one_div_le_one_div_of_le hk1 h_factored
        -- 1/(δ_k (1 - ω δ_k)) ≥ 1/δ_k + ω: algebra gives a nonneg residual.
        have h_geom :
            1 / (f (x k) - f xstar) + ω
              ≤ 1 / ((f (x k) - f xstar) * (1 - ω * (f (x k) - f xstar))) := by
          rw [← sub_nonneg]
          have hk_ne : f (x k) - f xstar ≠ 0 := ne_of_gt hk_pos
          have hone_ne : 1 - ω * (f (x k) - f xstar) ≠ 0 := ne_of_gt h_one_minus_pos
          have hf_eq :
              1 / ((f (x k) - f xstar) * (1 - ω * (f (x k) - f xstar)))
                - (1 / (f (x k) - f xstar) + ω)
              = (ω ^ 2 * (f (x k) - f xstar))
                / (1 - ω * (f (x k) - f xstar)) := by
            field_simp [hk_ne, hone_ne]
            ring
          rw [hf_eq]
          exact div_nonneg (by positivity) h_one_minus_pos.le
        -- Combine: ω (k+1) = ω k + ω ≤ 1/δ_k + ω ≤ 1/(δ_k(1-ω δ_k)) ≤ 1/δ_{k+1}.
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        have hsplit : ω * ((k : ℝ) + 1) = ω * (k : ℝ) + ω := by ring
        rw [hcast, hsplit]
        linarith [h_inv, h_inv_step, h_geom]
      · push_neg at hk1
        left
        linarith [hk1, hδk1_nonneg]

/-- Lu-BDA Thm 11.1 (gradient-descent convergence rate). Convex `L`-smooth `f`,
step `1/L`, global minimizer `x*`: `f(x_t) - f(x*) ≤ 2L‖x_0 - x*‖²/t` for
`t ≥ 1`. The constant matches the book exactly (the proof goes through a
slightly tighter pre-bound that is then loosened to match the book). -/
theorem gradientDescent_rate
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    (x : ℕ → E) (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y)
    {t : ℕ} (ht : 0 < t) :
    f (x t) - f xstar ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / (t : ℝ) := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hRHS_nonneg : 0 ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / (t : ℝ) := by positivity
  by_cases hD : ‖x 0 - xstar‖ ^ 2 = 0
  · -- Degenerate: x_0 = x* ⇒ x_t = x* for all t.
    have hD_norm : ‖x 0 - xstar‖ = 0 := sq_eq_zero_iff.mp hD
    have hx0_sub : x 0 - xstar = 0 := norm_eq_zero.mp hD_norm
    have hx0 : x 0 = xstar := sub_eq_zero.mp hx0_sub
    have hxt : x t = xstar :=
      gd_iterate_eq_xstar_of_start hdiff hrec hmin hx0 t
    rw [hxt, sub_self]
    exact hRHS_nonneg
  · -- Non-degenerate: apply the inverse-gap bound.
    have hD_pos : 0 < ‖x 0 - xstar‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hD)
    obtain h_zero | ⟨h_pos, h_inv⟩ :=
      gd_inv_gap_bound hf hdiff hL hsmooth hrec hmin hD_pos t
    · linarith [hRHS_nonneg]
    · have hω_pos : 0 < 1 / (2 * L * ‖x 0 - xstar‖ ^ 2) := by positivity
      have hωt_pos : 0 < (1 / (2 * L * ‖x 0 - xstar‖ ^ 2)) * (t : ℝ) :=
        mul_pos hω_pos ht_pos
      -- δ_t · (ω t) ≤ δ_t · (1/δ_t) = 1.
      have h_prod_le :
          (f (x t) - f xstar) * ((1 / (2 * L * ‖x 0 - xstar‖ ^ 2)) * (t : ℝ)) ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left h_inv h_pos.le
        rw [mul_one_div, div_self h_pos.ne'] at hmul
        linarith
      -- 1/(ω t) = 2L‖x_0 - x*‖² / t.
      have h_inv_eq :
          1 / ((1 / (2 * L * ‖x 0 - xstar‖ ^ 2)) * (t : ℝ))
            = 2 * L * ‖x 0 - xstar‖ ^ 2 / (t : ℝ) := by
        rw [div_mul_eq_mul_div, one_mul, one_div, inv_div]
      rw [← h_inv_eq, le_div_iff₀ hωt_pos]
      linarith [h_prod_le]

end StatLean.Optimization
