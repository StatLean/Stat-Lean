import StatLean.Optimization.Prox.Defs
import StatLean.Optimization.Smoothness.Defs
import StatLean.Optimization.ForMathlib.FirstOrderConvex

/-!
# The pillar inequality (Lemma 12.1)

The fundamental inequality behind both proximal-gradient convergence theorems
(Lu, *Big Data Analysis* §12.1, Lemma `lm:pillar`): for convex `L`-smooth `f`,
convex `h`, `F = f + h`, and a single proximal step
`y⁺ = prox_{(1/L)h}(y - (1/L)∇f y)`,
`F y⁺ - F x ≤ (L/2)‖x - y‖² - (L/2)‖x - y⁺‖²` for every `x`.

The proof combines:
* L-smoothness of `f` at `y⁺` vs `y`;
* convexity (gradient inequality) of `f` at `y` vs `x`;
* the variational inequality of the prox step (`prox_variational_inequality`
  below), which plays the role of the subgradient optimality
  `0 ∈ ∇f y + L(y⁺ - y) + ∂h(y⁺)` in the book, but is derived purely from
  convexity of `h` and the minimization property — no subgradient existence
  needed.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Variational inequality of the proximal minimizer. If `z = prox_h(x)` and `h`
is convex, then `⟪x - z, w - z⟫ ≤ h w - h z` for all `w`. This is the
first-order optimality of the prox subproblem, obtained from a convex
perturbation `proxObj h x z ≤ proxObj h x (z + t(w - z))` letting `t → 0⁺`. -/
theorem prox_variational_inequality
    {h : E → ℝ} (hh : ConvexOn ℝ Set.univ h) {x z : E}
    (hz : IsProxMinimizer h x z) (w : E) :
    ⟪x - z, w - z⟫_ℝ ≤ h w - h z := by
  -- Per-`t` inequality from the convex perturbation `z + t(w-z)`.
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      h z - h w - ⟪z - x, w - z⟫_ℝ ≤ t / 2 * ‖w - z‖ ^ 2 := by
    intro t ht0 ht1
    have hcc : z + t • (w - z) = (1 - t) • z + t • w := by module
    -- convexity of `h` at the combination
    have hconv : h (z + t • (w - z)) ≤ (1 - t) * h z + t * h w := by
      rw [hcc]
      have hcvx := hh.2 (Set.mem_univ z) (Set.mem_univ w)
        (by linarith : (0:ℝ) ≤ 1 - t) (le_of_lt ht0) (by ring)
      simpa using hcvx
    -- minimality of the prox point at the perturbed point
    have hmin := hz (z + t • (w - z))
    simp only [proxObj] at hmin
    have hexp : ‖z + t • (w - z) - x‖ ^ 2
        = ‖z - x‖ ^ 2 + 2 * t * ⟪z - x, w - z⟫_ℝ + t ^ 2 * ‖w - z‖ ^ 2 := by
      have hrw : z + t • (w - z) - x = (z - x) + t • (w - z) := by abel
      rw [hrw, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
      ring
    rw [hexp] at hmin
    -- combine and divide by `t`
    have hcomb : t * (h z - h w - ⟪z - x, w - z⟫_ℝ) ≤ t * (t / 2 * ‖w - z‖ ^ 2) := by
      nlinarith [hmin, hconv]
    have := le_of_mul_le_mul_left hcomb ht0
    linarith
  -- Let `t → 0⁺`.
  have hC : h z - h w - ⟪z - x, w - z⟫_ℝ ≤ 0 := by
    have hKnn : (0:ℝ) ≤ ‖w - z‖ ^ 2 := sq_nonneg _
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨t, ht0, ht1, htK⟩ :
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t / 2 * ‖w - z‖ ^ 2 ≤ ε := by
      rcases eq_or_lt_of_le hKnn with hK0 | hKpos
      · exact ⟨1, one_pos, le_rfl, by rw [← hK0]; simpa using hε.le⟩
      · refine ⟨min 1 (ε / ‖w - z‖ ^ 2), lt_min one_pos (by positivity),
          min_le_left _ _, ?_⟩
        have hle : min 1 (ε / ‖w - z‖ ^ 2) ≤ ε / ‖w - z‖ ^ 2 := min_le_right _ _
        have h1 : min 1 (ε / ‖w - z‖ ^ 2) * ‖w - z‖ ^ 2 ≤ ε := by
          calc min 1 (ε / ‖w - z‖ ^ 2) * ‖w - z‖ ^ 2
              ≤ (ε / ‖w - z‖ ^ 2) * ‖w - z‖ ^ 2 :=
                mul_le_mul_of_nonneg_right hle hKpos.le
            _ = ε := by field_simp
        nlinarith [h1, hε]
    calc h z - h w - ⟪z - x, w - z⟫_ℝ ≤ t / 2 * ‖w - z‖ ^ 2 := key t ht0 ht1
      _ ≤ ε := htK
      _ = 0 + ε := (zero_add _).symm
  have hflip : ⟪x - z, w - z⟫_ℝ = -⟪z - x, w - z⟫_ℝ := by
    rw [← inner_neg_left]; congr 1; abel
  rw [hflip]; linarith

/-- Pillar inequality (Lu-BDA Lemma 12.1). For convex `L`-smooth `f` (`0 < L`),
convex `h`, and the prox step `y⁺ = prox_{(1/L)h}(y - (1/L)∇f y)`,
`(f y⁺ + h y⁺) - (f x + h x) ≤ (L/2)‖x - y‖² - (L/2)‖x - y⁺‖²`. -/
theorem pillar
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    {x y yplus : E}
    (hyplus : IsProxMinimizer ((1 / L) • h) (y - (1 / L) • gradient f y) yplus) :
    (f yplus + h yplus) - (f x + h x)
      ≤ (L / 2) * ‖x - y‖ ^ 2 - (L / 2) * ‖x - yplus‖ ^ 2 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  set g := gradient f y with hg
  -- (S) L-smoothness of `f` at `(y, y⁺)`.
  have hS : f yplus ≤ f y + ⟪g, yplus - y⟫_ℝ + L / 2 * ‖y - yplus‖ ^ 2 := hsmooth y yplus
  -- (C) convexity (gradient inequality) of `f` at `(y, x)`.
  have hCf : f y + ⟪g, x - y⟫_ℝ ≤ f x := inner_gradient_le_sub_of_convexOn hf hdiff y x
  -- (V) prox variational inequality for `(1/L)•h`, scaled by `L`.
  have hconv_h : ConvexOn ℝ Set.univ ((1 / L) • h) := hh.smul (by positivity)
  have hV := prox_variational_inequality hconv_h hyplus x
  simp only [Pi.smul_apply, smul_eq_mul] at hV
  have hVexp : ⟪y - (1 / L) • g - yplus, x - yplus⟫_ℝ
      = ⟪y - yplus, x - yplus⟫_ℝ - 1 / L * ⟪g, x - yplus⟫_ℝ := by
    rw [show y - (1 / L) • g - yplus = (y - yplus) - (1 / L) • g by abel,
      inner_sub_left, real_inner_smul_left]
  rw [hVexp] at hV
  have hV' : h yplus - h x ≤ ⟪g, x - yplus⟫_ℝ - L * ⟪y - yplus, x - yplus⟫_ℝ := by
    have hmul := mul_le_mul_of_nonneg_left hV hL.le
    have hsimpL : ∀ c : ℝ, L * (1 / L * c) = c := fun c => by field_simp
    rw [mul_sub, mul_sub, hsimpL, hsimpL, hsimpL] at hmul
    linarith [hmul]
  -- inner-product bookkeeping
  have ig1 : ⟪g, yplus - y⟫_ℝ - ⟪g, x - y⟫_ℝ = ⟪g, yplus - x⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  have ig2 : ⟪g, yplus - x⟫_ℝ + ⟪g, x - yplus⟫_ℝ = 0 := by
    rw [← inner_add_right, show yplus - x + (x - yplus) = (0 : E) by abel, inner_zero_right]
  -- polarization identity
  have hpol : L / 2 * ‖y - yplus‖ ^ 2 - L * ⟪y - yplus, x - yplus⟫_ℝ
      = L / 2 * ‖x - y‖ ^ 2 - L / 2 * ‖x - yplus‖ ^ 2 := by
    have e1 : ‖x - y‖ ^ 2
        = ‖x - yplus‖ ^ 2 + 2 * ⟪x - yplus, yplus - y⟫_ℝ + ‖yplus - y‖ ^ 2 := by
      rw [show x - y = (x - yplus) + (yplus - y) by abel, norm_add_sq_real]
    have e2 : ‖y - yplus‖ ^ 2 = ‖yplus - y‖ ^ 2 := by rw [← norm_neg]; congr 1; abel
    have e3 : ⟪y - yplus, x - yplus⟫_ℝ = -⟪x - yplus, yplus - y⟫_ℝ := by
      rw [real_inner_comm, ← inner_neg_right]; congr 1; abel
    rw [e1, e2, e3]; ring
  linarith [hS, hCf, hV', ig1, ig2, hpol]

end StatLean.Optimization
