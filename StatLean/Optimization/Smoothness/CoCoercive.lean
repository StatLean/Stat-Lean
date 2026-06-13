import StatLean.Optimization.Smoothness.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# Co-coercivity of the gradient (Lemma 11.1)

For a convex `L`-smooth function, the gradient satisfies the co-coercivity
inequality (Lu, *Big Data Analysis* §11.1, Lemma 11.1):
`f x - f y ≤ ⟪∇f x, x - y⟫ - (1/(2L)) ‖∇f x - ∇f y‖²`.

The book states it for `L`-smooth `f`, but its proof (evaluate the smoothness
upper bound at `z = y - (1/L)(∇f y - ∇f x)` and add the convexity inequality)
also uses convexity. We therefore state both hypotheses — a deliberate
hypothesis correction over the book text.

This is the key lemma behind the monotone-distance step of the gradient-descent
rate (Theorem 11.1).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Co-coercivity (Lu-BDA Lemma 11.1). For convex `L`-smooth `f` with `0 < L`:
`f x - f y ≤ ⟪∇f x, x - y⟫ - (1/(2L)) ‖∇f x - ∇f y‖²`. -/
theorem cocoercive
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (x y : E) :
    f x - f y ≤ ⟪gradient f x, x - y⟫_ℝ
      - (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2 := by
  set z : E := y + (1 / L) • (gradient f x - gradient f y) with hz_def
  -- Convexity at (x, z) and L-smoothness at (y, z).
  have hconv : f x + ⟪gradient f x, z - x⟫_ℝ ≤ f z :=
    inner_gradient_le_sub_of_convexOn hf hdiff x z
  have hsm : f z ≤ f y + ⟪gradient f y, z - y⟫_ℝ + (L / 2) * ‖y - z‖ ^ 2 :=
    hsmooth y z
  -- Vector identities at the additive-group level.
  have hzy_eq : z - y = (1 / L) • (gradient f x - gradient f y) := by
    rw [hz_def]; abel
  have hyz_eq : y - z = -((1 / L) • (gradient f x - gradient f y)) := by
    rw [hz_def]; abel
  have hxz_eq : x - z = (x - y) - (1 / L) • (gradient f x - gradient f y) := by
    rw [hz_def]; abel
  -- Norm/scaling identity: (L/2)‖y-z‖² = (1/(2L))‖∇f x - ∇f y‖².
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hL_inv_pos : (0 : ℝ) < 1 / L := by positivity
  have h_norm_yz :
      (L / 2) * ‖y - z‖ ^ 2 = (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2 := by
    rw [hyz_eq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hL_inv_pos]
    field_simp
    ring
  -- Inner-product expansions of the two RHS pieces.
  have h_inner_xz :
      ⟪gradient f x, x - z⟫_ℝ
        = ⟪gradient f x, x - y⟫_ℝ
          - (1 / L) * ⟪gradient f x, gradient f x - gradient f y⟫_ℝ := by
    rw [hxz_eq, inner_sub_right, real_inner_smul_right]
  have h_inner_zy :
      ⟪gradient f y, z - y⟫_ℝ
        = (1 / L) * ⟪gradient f y, gradient f x - gradient f y⟫_ℝ := by
    rw [hzy_eq, real_inner_smul_right]
  -- Rewrite convexity as `f x - f z ≤ ⟪∇f x, x - z⟫`.
  have hneg_zx :
      ⟪gradient f x, x - z⟫_ℝ = -⟪gradient f x, z - x⟫_ℝ := by
    rw [← inner_neg_right]
    congr 1
    abel
  have hconv' : f x - f z ≤ ⟪gradient f x, x - z⟫_ℝ := by
    linarith [hconv, hneg_zx]
  -- Sum: f x - f y ≤ ⟪∇f x, x-z⟫ + ⟪∇f y, z-y⟫ + (L/2)‖y-z‖².
  have hsum :
      f x - f y
        ≤ ⟪gradient f x, x - z⟫_ℝ + ⟪gradient f y, z - y⟫_ℝ + (L / 2) * ‖y - z‖ ^ 2 := by
    linarith [hconv', hsm]
  rw [h_inner_xz, h_inner_zy, h_norm_yz] at hsum
  -- Inner-product cross-term identity: A - B = ‖g‖² for g = ∇f x - ∇f y.
  have h_inner_diff :
      ⟪gradient f x, gradient f x - gradient f y⟫_ℝ
        - ⟪gradient f y, gradient f x - gradient f y⟫_ℝ
      = ‖gradient f x - gradient f y‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  -- Combine: (1/L)*A - (1/L)*B = (1/L)*‖g‖².
  have h_combined :
      (1 / L) * ⟪gradient f x, gradient f x - gradient f y⟫_ℝ
        - (1 / L) * ⟪gradient f y, gradient f x - gradient f y⟫_ℝ
      = (1 / L) * ‖gradient f x - gradient f y‖ ^ 2 := by
    rw [← mul_sub, h_inner_diff]
  -- Coefficient identity: 2·(1/(2L)) = 1/L.
  have h_coef :
      (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2
        + (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2
      = (1 / L) * ‖gradient f x - gradient f y‖ ^ 2 := by
    field_simp
    ring
  linarith [hsum, h_combined, h_coef]

/-- Monotonicity of the gradient (immediate corollary of co-coercivity):
`(1/(2L)) ‖∇f x - ∇f y‖² ≤ ⟪∇f x - ∇f y, x - y⟫` (Lu-BDA §11.1). -/
theorem inner_gradient_sub_nonneg
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (x y : E) :
    (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2
      ≤ ⟪gradient f x - gradient f y, x - y⟫_ℝ := by
  have h1 := cocoercive hf hdiff hL hsmooth x y
  have h2 := cocoercive hf hdiff hL hsmooth y x
  -- Symmetrize the gradient-norm in h2.
  have h_norm_swap :
      ‖gradient f y - gradient f x‖ = ‖gradient f x - gradient f y‖ := by
    rw [← norm_neg]; congr 1; abel
  rw [h_norm_swap] at h2
  -- ⟪∇f x, x-y⟫ + ⟪∇f y, y-x⟫ = ⟪∇f x - ∇f y, x-y⟫.
  have h_inner_split :
      ⟪gradient f x, x - y⟫_ℝ + ⟪gradient f y, y - x⟫_ℝ
      = ⟪gradient f x - gradient f y, x - y⟫_ℝ := by
    rw [inner_sub_left]
    have hneg : ⟪gradient f y, y - x⟫_ℝ = -⟪gradient f y, x - y⟫_ℝ := by
      rw [← inner_neg_right]; congr 1; abel
    linarith [hneg]
  -- Coefficient identity: 2·(1/(2L)) = 1/L.
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have h_coef :
      (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2
        + (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2
      = (1 / L) * ‖gradient f x - gradient f y‖ ^ 2 := by
    field_simp
    ring
  have h_nonneg : 0 ≤ (1 / (2 * L)) * ‖gradient f x - gradient f y‖ ^ 2 := by
    have hL2_pos : (0 : ℝ) < 2 * L := by positivity
    positivity
  linarith [h1, h2, h_inner_split, h_coef, h_nonneg]

end StatLean.Optimization
