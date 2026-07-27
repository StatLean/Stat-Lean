import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
import StatLean.HypothesisTesting.ForMathlib.GaussianShell
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# A multivariate Berry–Esseen bound via Lindeberg swapping (honest, non-sharp)

This file develops the elementary "smooth the indicator + Lindeberg swap" route to a
multivariate Berry–Esseen bound, as suggested for
`StatLean.HypothesisTesting.GoodnessOfFit.SmoothTestLargeK`. The two statements quoted
there, `bentkus_berry_esseen_convex` (constant `400 k^{1/4}`) and
`bentkus_berry_esseen_ball` (dimension-free `C`), are **Bentkus (2003)**: a sharp,
research-level dimension factor obtained by Fourier analysis over convex bodies. Their sharp
`β/√n` *rate* is not reproduced here; what is proved here is the honest elementary rate
`(β/√n)^{1/4}`, over balls (`berryEsseen_ball_elementary`, which discharges
`bentkus_berry_esseen_ball`) and over convex sets (`berryEsseen_convex_elementary`).

What this file records instead is the strongest bound the elementary route yields *honestly*.
The single ingredient that is proved unconditionally and is genuinely dimension-free is the
**Gaussian slab (half-space) anti-concentration** bound:

`gaussian_slab_measure_le` — for a unit vector `u` and `a ≤ b`,
`N(0, I_k)({z : a < ⟪u,z⟫ ≤ b}) ≤ (b - a) / √(2π)`,

whose constant `1/√(2π)` carries **no dimension factor at all**. This is "step 3" of the
route for a half-space, and it is the one-dimensional marginal statement: the projection
`z ↦ ⟪u,z⟫` of `N(0,I_k)` is exactly `N(0,1)`, whose density is bounded by `1/√(2π)`.

## Honest accounting of the elementary route (see the module docstring below for the report)

For the **ball** route the elementary programme is now **complete**: `berryEsseen_ball_elementary`
is proved outright and is axiom-clean (it depends on no `sorry`, direct or transitive). Every
ingredient is proved here unconditionally, each with a dimension-free constant:

* `gaussian_slab_measure_le` — slab anti-concentration (`1/√(2π)`);
* `gaussian_ball_shell_measure_le` — *shell* anti-concentration (`C_ac = 7`), resting on the
  uniform chi-density peak bound `chiSquared_density_mul_sqrt_le`, which is obtained **without
  any Stirling asymptotics for `Γ`** by restricting Euler's integral to the length-`√p` window
  at the peak (`le_Gamma_add_half`);
* `norm_taylor_remainder_three_le` — the third-order Taylor remainder on a normed space
  (Mathlib v4.29.1 has only the one-dimensional version, so this is reduced to a segment);
* `exists_smoothed_radial_indicator` — the smoothed radial indicator with an absolute
  third-derivative constant, built by composing a fixed 1-D cutoff with `‖·‖²` (**not** with
  `‖·‖`), which avoids the quantitative iterated-derivative bounds for the Euclidean norm that
  Mathlib does not have.

* `map_normalized_sum_stdGaussian` — Gaussian stability of the normalized sum,
  `(⨂ⁿ N(0,I_k)).map (n^{-1/2} ∑) = N(0,I_k)`, the right-hand endpoint of the Lindeberg
  telescope. Proved by characteristic functions (`Measure.ext_of_charFun` plus the product
  factorization `charFun_map_const_smul_sum`), not by iterated convolution;
* `abs_integral_smooth_sub_gaussian_le` — the third-order multivariate **Lindeberg swap**: the
  hybrid telescope `Qⱼ = ⨂ᵢ (if i < j then γ else ν)`, each step isolated by
  `integral_pi_sum_peel` (`measurePreserving_piFinSuccAbove` + Fubini) and compared by
  `abs_integral_swap_step_le`. The one-step comparison is a second-order Taylor expansion in
  which the linear term dies by Riesz representation plus `hmean`
  (`integral_clm_eq_zero_of_centred`), the quadratic term takes the *same* value on both sides
  because both laws have identity covariance (`integral_bilin_eq_basis_sum` — note it never
  needs the value of that basis sum, only that it is the same one), and the remainder is
  `norm_taylor_remainder_three_le`.

With the Gaussian third moment `β_G ≤ 2 k^{3/2}` (`integral_norm_cube_gaussian_le`, from the two
public χ² moments) these suffice and the ball assembly closes.

The *convex* route is **now complete as well**: `berryEsseen_convex_elementary` is proved
outright and is axiom-clean. Its two ingredients are

* `exists_smoothed_convex_indicator` — the smoothed convex indicator (mollification by a
  `ContDiffBump`, dimension-dependent constant); see its docstring for the construction and the
  section preceding it for the `precompR` tower. With the Lindeberg swap it gives
  `berryEsseen_convex_levy_elementary`, the Lévy/Prokhorov form
  `μₙ(B) ≤ γ(Bᵋ) + C (β/√n)/ε³` (and its mirror image);
* the Gaussian **boundary-shell** bound `γ(Bᵋ) ≤ γ(B) + C_k ε` for convex `B`, together with its
  erosion twin `γ(B) ≤ γ(B₋ᵋ) + C_k ε`. These are `gaussian_thickening_le` and
  `gaussian_le_erosion_add` of `StatLean.HypothesisTesting.ForMathlib.GaussianShell`, proved
  there elementarily (convex slice + supporting hyperplane + `2k` coordinate shifts) with the
  explicit constant `C_k = 8 k^{3/2}/√(2π)`. Ball's Gaussian-surface-area theorem gives the
  sharp `4 k^{1/4}` — exactly the dimension factor of Bentkus's constant — but the assembly
  needs only finiteness of `C_k` at fixed `k`.

Crucially, the elementary balance of steps 2–3 still does **not** reach
the `β/√n` *rate* of the frozen statements: optimising `ε` in `ε^{-3} β/√n + C ε` gives an error
of order `(β/√n)^{1/4}`, i.e. `n^{-1/8}`, not `n^{-1/2}`. That is a genuine feature of the
mollifier method (the sharp rate needs characteristic functions / Esseen's smoothing lemma), and
it is reported precisely rather than papered over.

**Reference.** V. Bentkus, "On the dependence of the Berry–Esseen bound on dimension,"
*J. Statist. Plann. Inference* **113** (2003), 385–402. E. L. Lehmann and J. P. Romano,
*Testing Statistical Hypotheses*, 4th ed., Springer, 2022, §16.4, Lemma 16.4.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators InnerProductSpace Real

namespace StatLean.HypothesisTesting

/-! ### Gaussian slab anti-concentration (dimension-free) -/

section AntiConcentration

variable {k : ℕ}

/-- The pushforward of the standard multivariate Gaussian `N(0, I_k)` under a **unit-vector**
inner-product projection `z ↦ ⟪u, z⟫` is the standard one-dimensional Gaussian `N(0,1)`.
This is the marginal computation behind the anti-concentration bound. -/
lemma stdGaussian_map_inner_unit (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    Measure.map (fun y => ⟪u, y⟫_ℝ) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = gaussianReal 0 1 := by
  rw [multivariateGaussian_map_inner_eq_gaussianReal u Matrix.PosSemidef.one]
  congr 1
  have hstar : star u.ofLp = u.ofLp := by ext i; simp
  have huu : u.ofLp ⬝ᵥ (1 : Matrix (Fin k) (Fin k) ℝ).mulVec u.ofLp = 1 := by
    rw [Matrix.one_mulVec]
    calc u.ofLp ⬝ᵥ u.ofLp
        = u.ofLp ⬝ᵥ star u.ofLp := by rw [hstar]
      _ = ⟪u, u⟫_ℝ := (EuclideanSpace.inner_eq_star_dotProduct u u).symm
      _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
      _ = 1 := by rw [hu]; norm_num
  rw [huu, Real.toNNReal_one]

/-- **Standard 1-D Gaussian anti-concentration.** The `N(0,1)` mass of an interval `(a, b]`
is at most `(b - a)/√(2π)`, because the Gaussian density is bounded by `1/√(2π)`. -/
lemma gaussianReal_stdNormal_Ioc_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1 (Set.Ioc a b)).toReal ≤ (b - a) / Real.sqrt (2 * π) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_apply_eq_integral 0 hv (Set.Ioc a b), ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Ioc (fun x _ => gaussianPDFReal_nonneg _ _ _))]
  have hbound : ∀ x, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * π))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (x - 0)]
    have hpos : (0 : ℝ) ≤ (Real.sqrt (2 * π * 1))⁻¹ := by positivity
    calc gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π * 1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 1)) := rfl
      _ ≤ (Real.sqrt (2 * π * 1))⁻¹ * 1 := by
            apply mul_le_mul_of_nonneg_left hexp hpos
      _ = (Real.sqrt (2 * π))⁻¹ := by norm_num
  calc ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x
      ≤ ∫ _ in Set.Ioc a b, (Real.sqrt (2 * π))⁻¹ ∂volume := by
          apply setIntegral_mono_on (integrable_gaussianPDFReal _ _).restrict
            (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
          exact fun x _ => hbound x
    _ = (b - a) / Real.sqrt (2 * π) := by
          rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring

/-- **Gaussian slab anti-concentration, dimension-free.** For a unit vector `u` and `a ≤ b`,
the standard multivariate Gaussian mass of the slab `{z : a < ⟪u,z⟫ ≤ b}` is at most
`(b - a)/√(2π)`. The constant carries no dimension factor: this is "step 3" of the Lindeberg
route for a half-space, and is exactly the one-dimensional marginal bound.

This is the honest ingredient the elementary convex-set Berry–Esseen argument would consume;
the dimension factor of Bentkus (2003) arises only from covering the boundary shell of a
general convex body by such slabs, which is not carried out here. -/
theorem gaussian_slab_measure_le (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)
    {a b : ℝ} (hab : a ≤ b) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
        {z | a < ⟪u, z⟫_ℝ ∧ ⟪u, z⟫_ℝ ≤ b}).toReal
      ≤ (b - a) / Real.sqrt (2 * π) := by
  have hset : {z : EuclideanSpace ℝ (Fin k) | a < ⟪u, z⟫_ℝ ∧ ⟪u, z⟫_ℝ ≤ b}
      = (fun y => ⟪u, y⟫_ℝ) ⁻¹' Set.Ioc a b := rfl
  rw [hset, ← Measure.map_apply (by fun_prop) measurableSet_Ioc,
    stdGaussian_map_inner_unit u hu]
  exact gaussianReal_stdNormal_Ioc_le hab

end AntiConcentration

/-! ### Dimension-free ball anti-concentration (the radial analogue)

For the *ball* route the relevant anti-concentration statement is the mass of a thin spherical
**shell** `{t < ‖z‖ ≤ t + ε}` under `N(0, I_k)`. Its clean reduction is that the law of `‖z‖²`
under `N(0, I_k)` is exactly the chi-squared law `χ²_k`, so the shell mass is a chi-squared
interval mass. The genuinely dimension-free fact is that the **chi density** `f_k(r) = c_k r^{k-1}
e^{-r²/2}` (equivalently `2√x · gammaPDF (k/2) (1/2) x`) has a maximum bounded by an *absolute*
constant, uniformly in `k` — its peak `≈ e^{1/2}/√π < 1` sits at `r = √(k-1)` and does not grow
with `k`. That single uniform bound (`chiSquared_density_mul_sqrt_le`) is the crux; everything else
is the measure-theoretic reduction and an elementary `∫ 1/(2√x) dx = √x` computation.

Both are now proved: the peak bound is obtained **without any Stirling asymptotics** for `Γ` by
restricting Euler's integral to the length-`√p` window `(p, p+√p]` at the peak
(`le_Gamma_add_half`), which is enough because the window's own width supplies exactly the
`√p/√(3p) = 1/√3` that the `x^{-1/2}` factor costs. The resulting absolute constant is
`e√6 < 7`. -/

section BallAntiConcentration

open scoped Real

variable {k : ℕ}

/-- **Shell mass is a chi-squared interval mass.** For `0 < k`, `0 ≤ t`, `0 ≤ ε`, the standard
multivariate Gaussian mass of the spherical shell `{t < ‖z‖ ≤ t + ε}` equals the chi-squared mass
of the interval `(t², (t+ε)²]`, because `‖z‖² ∼ χ²_k` under `N(0, I_k)` and `r ↦ r²` is strictly
monotone on `[0, ∞)`. -/
lemma multivariateGaussian_shell_eq_chiSquared (hk : 0 < k) {t ε : ℝ} (ht : 0 ≤ t)
    (hε : 0 ≤ ε) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 {z | t < ‖z‖ ∧ ‖z‖ ≤ t + ε}
      = StatLean.MultipleTesting.chiSquared k (Set.Ioc (t ^ 2) ((t + ε) ^ 2)) := by
  have hmap : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map (fun z => ‖z‖ ^ 2)
      = StatLean.MultipleTesting.chiSquared k := by
    rw [map_normSq_multivariateGaussian_of_norm_eq k 0 (by simp), noncentralChiSquared_zero hk]
  have hset : {z : EuclideanSpace ℝ (Fin k) | t < ‖z‖ ∧ ‖z‖ ≤ t + ε}
      = (fun z => ‖z‖ ^ 2) ⁻¹' Set.Ioc (t ^ 2) ((t + ε) ^ 2) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc]
    have hz : 0 ≤ ‖z‖ := norm_nonneg z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  rw [hset, ← Measure.map_apply (by fun_prop) measurableSet_Ioc, hmap]

/-- The elementary primitive `√x` of `1/(2√x)`: for `0 ≤ a ≤ b`,
`∫_{(a,b]} (2√x)⁻¹ dx = √b − √a`. This is the change-of-variables factor that turns the
chi-squared interval width `(t+ε)² − t²` back into the shell width `ε`. -/
lemma integral_Ioc_inv_two_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (2 * Real.sqrt x)⁻¹ = Real.sqrt b - Real.sqrt a := by
  rw [← intervalIntegral.integral_of_le hab]
  have hcont : ContinuousOn Real.sqrt (Set.Icc a b) := Real.continuous_sqrt.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivWithinAt Real.sqrt ((2 * Real.sqrt x)⁻¹) (Set.Ioi x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hx.1)
    have h := (Real.hasDerivAt_sqrt hx0).hasDerivWithinAt (s := Set.Ioi x)
    rwa [one_div] at h
  have hint : IntervalIntegrable (fun x => (2 * Real.sqrt x)⁻¹) volume a b := by
    have hrpow : IntervalIntegrable (fun x => (1 / 2) * x ^ (-(1 / 2) : ℝ)) volume a b :=
      (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (1 / 2)
    refine (intervalIntegrable_congr (fun x hx => ?_)).mp hrpow
    have hx0 : 0 < x := by
      rw [Set.uIoc_of_le hab] at hx; exact lt_of_le_of_lt ha hx.1
    rw [Real.sqrt_eq_rpow, mul_inv, Real.rpow_neg hx0.le]; ring
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint

/-- **Peak of the gamma kernel.** For `p > 0` the function `x ↦ x^p e^{-x/2}` attains its
maximum over `x > 0` at `x = 2p`. Taking logarithms this is exactly `log t ≤ t - 1` at
`t = x/(2p)`. -/
private lemma rpow_mul_exp_neg_half_le {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    x ^ p * Real.exp (-x / 2) ≤ (2 * p) ^ p * Real.exp (-p) := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have h2p : (0 : ℝ) < 2 * p := by linarith
  have hlog : Real.log (x / (2 * p)) ≤ x / (2 * p) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt h2p)] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have hxx : p * (x / (2 * p) - 1) = x / 2 - p := by field_simp
  rw [hxx] at hmul
  have hL : x ^ p * Real.exp (-x / 2) = Real.exp (p * Real.log x - x / 2) := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]; congr 1; ring
  have hR : (2 * p) ^ p * Real.exp (-p) = Real.exp (p * Real.log (2 * p) - p) := by
    rw [Real.rpow_def_of_pos h2p, ← Real.exp_add]; congr 1; ring
  rw [hL, hR]
  exact Real.exp_le_exp.mpr (by nlinarith [hmul])

/-- **Stirling-free lower bound for `Γ` at the half-integer shift.** For `p ≥ 1/2`,
`Γ(p + 1/2) ≥ p^p e^{-p} / (e √3)`.

This replaces the `Γ`-Stirling estimate that Mathlib v4.29.1 does not provide for
half-integer arguments: instead of asymptotics one simply restricts Euler's integral
`Γ(p+1/2) = ∫_{x>0} e^{-x} x^{p-1/2} dx` to the window `(p, p + √p]` of length `√p` sitting at
the peak. On that window `e^{-x} x^p ≥ p^p e^{-p} e^{-1}` (from `log t ≥ 1 - 1/t`, since
`(x-p)² ≤ p < x` there) and `x^{-1/2} ≥ (3p)^{-1/2}` (since `x ≤ p + √p ≤ 3p` for `p ≥ 1/4`);
multiplying by the window length `√p` gives `√p/√(3p) = 1/√3`. -/
private lemma le_Gamma_add_half {p : ℝ} (hp : 1 / 2 ≤ p) :
    p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3) ≤ Real.Gamma (p + 1 / 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hspsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hsple : Real.sqrt p ≤ 2 * p := by nlinarith [hspsq, hsp]
  have hs : (0 : ℝ) < p + 1 / 2 := by linarith
  have hGam : Real.Gamma (p + 1 / 2)
      = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (p + 1 / 2 - 1) :=
    Real.Gamma_eq_integral hs
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (p + 1 / 2 - 1))
      (Set.Ioi 0) := Real.GammaIntegral_convergent hs
  set L : ℝ := p ^ p * Real.exp (-p) * Real.exp (-1) * (Real.sqrt (3 * p))⁻¹ with hLdef
  have hsub : Set.Ioc p (p + Real.sqrt p) ⊆ Set.Ioi (0 : ℝ) := fun y hy => lt_trans hp0 hy.1
  -- Pointwise lower bound of the Euler integrand on the peak window.
  have hpt : ∀ y ∈ Set.Ioc p (p + Real.sqrt p), L ≤ Real.exp (-y) * y ^ (p + 1 / 2 - 1) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy0 : (0 : ℝ) < y := lt_trans hp0 hy1
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hsplit : y ^ (p + 1 / 2 - 1) = y ^ p * (Real.sqrt y)⁻¹ := by
      rw [show p + 1 / 2 - 1 = p - 1 / 2 by ring, Real.rpow_sub hy0, Real.sqrt_eq_rpow,
        div_eq_mul_inv]
    -- (a) the exponential–power factor is within `e` of its peak value
    have hA : p ^ p * Real.exp (-p) * Real.exp (-1) ≤ Real.exp (-y) * y ^ p := by
      have hlt : Real.log (p / y) ≤ p / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hp0) (ne_of_gt hy0)] at hlt
      have hmul := mul_le_mul_of_nonneg_left hlt hp0.le
      have hpy : p * (p / y - 1) = p ^ 2 / y - p := by field_simp
      rw [hpy] at hmul
      have hd : (y - p) ^ 2 ≤ y := by nlinarith [hspsq]
      have hyy : p ^ 2 / y ≤ 2 * p + 1 - y := by
        rw [div_le_iff₀ hy0]; nlinarith [hd]
      have hlogineq : p * Real.log p - p - 1 ≤ -y + p * Real.log y := by linarith
      have hE1 : p ^ p * Real.exp (-p) * Real.exp (-1)
          = Real.exp (p * Real.log p - p - 1) := by
        rw [Real.rpow_def_of_pos hp0, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hE2 : Real.exp (-y) * y ^ p = Real.exp (-y + p * Real.log y) := by
        rw [Real.rpow_def_of_pos hy0, ← Real.exp_add]; congr 1; ring
      rw [hE1, hE2]
      exact Real.exp_le_exp.mpr hlogineq
    -- (b) the radial factor `x^{-1/2}` is at least `(3p)^{-1/2}` on the window
    have hB : (Real.sqrt (3 * p))⁻¹ ≤ (Real.sqrt y)⁻¹ := by
      have h1 : Real.sqrt y ≤ Real.sqrt (3 * p) := Real.sqrt_le_sqrt (by linarith)
      exact inv_anti₀ hsy h1
    rw [hsplit, hLdef]
    calc p ^ p * Real.exp (-p) * Real.exp (-1) * (Real.sqrt (3 * p))⁻¹
        ≤ p ^ p * Real.exp (-p) * Real.exp (-1) * (Real.sqrt y)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ Real.exp (-y) * y ^ p * (Real.sqrt y)⁻¹ :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = Real.exp (-y) * (y ^ p * (Real.sqrt y)⁻¹) := by ring
  -- Integrate the pointwise bound over the window and drop to the whole half-line.
  have hIc : IntegrableOn (fun _ : ℝ => L) (Set.Ioc p (p + Real.sqrt p)) :=
    integrableOn_const (C := L) measure_Ioc_lt_top.ne
  have hIf : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ (p + 1 / 2 - 1))
      (Set.Ioc p (p + Real.sqrt p)) := hint.mono_set hsub
  have hwin : L * Real.sqrt p ≤ ∫ y in Set.Ioc p (p + Real.sqrt p),
      Real.exp (-y) * y ^ (p + 1 / 2 - 1) := by
    have hmono := setIntegral_mono_on hIc hIf measurableSet_Ioc hpt
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith [Real.sqrt_nonneg p]), smul_eq_mul] at hmono
    calc L * Real.sqrt p = (p + Real.sqrt p - p) * L := by ring
      _ ≤ _ := hmono
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun x : ℝ => Real.exp (-x) * x ^ (p + 1 / 2 - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx0.le _)
  have hLid : L * Real.sqrt p = p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3) := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    rw [hLdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) p,
      show Real.exp (-1) = (Real.exp 1)⁻¹ from Real.exp_neg 1]
    have hsne : Real.sqrt p ≠ 0 := ne_of_gt hsp
    have h3ne : Real.sqrt 3 ≠ 0 := ne_of_gt h3
    have hene : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
    field_simp
  rw [hGam, ← hLid]
  exact hwin.trans (setIntegral_mono_set hint hnn hsub.eventuallyLE)

/-- Numerical constant of the peak bound: `2 (√2)⁻¹ e √3 = e √6 < 7`. -/
private lemma peak_const_le_seven :
    2 * (Real.sqrt 2)⁻¹ * (Real.exp 1 * Real.sqrt 3) ≤ 7 := by
  have h2 : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h3 : Real.sqrt 3 ≤ 1.7321 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hinv : (Real.sqrt 2)⁻¹ ≤ (1.414 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hs3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hinv0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  calc 2 * (Real.sqrt 2)⁻¹ * (Real.exp 1 * Real.sqrt 3)
      ≤ 2 * (1.414 : ℝ)⁻¹ * (2.7182818286 * 1.7321) := by gcongr
    _ ≤ 7 := by norm_num

/-- **The dimension-free chi-density peak bound.**
`2√x · gammaPDF (k/2) (1/2) x ≤ 7` for all `k > 0` and `x > 0`. The left side is exactly the chi
density `f_k(√x) = √x^{k-1} e^{-x/2} / (2^{k/2-1} Γ(k/2))`; its maximum over `x` is attained at
`x = k-1` with value `→ e^{1/2}/√π < 1` as `k → ∞`, and the proof below shows it never exceeds
`e√6 < 7`. **This is the one genuinely dimension-free crux of the ball route.**

Proof. Write `a = k/2` and `p = a - 1/2`. Then
`2√x · gammaPDFReal a (1/2) x = 2 (1/2)^a Γ(a)⁻¹ · x^p e^{-x/2}`; the kernel factor is maximised
at `x = 2p` (`rpow_mul_exp_neg_half_le`), and `(1/2)^a (2p)^p = (√2)⁻¹ p^p`, so the whole
expression is at most `√2 · p^p e^{-p} / Γ(p + 1/2)`, which `le_Gamma_add_half` bounds by
`√2 · e √3 = e √6 < 7` — with **no dependence on `k`**. The degenerate case `k = 1` (`p = 0`) is
separate and uses `Γ(1/2) = √π`. -/
private lemma chiSquared_density_mul_sqrt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 0 < k → ∀ x : ℝ, 0 < x →
      2 * Real.sqrt x * gammaPDFReal ((k : ℝ) / 2) (1 / 2) x ≤ C := by
  refine ⟨7, by norm_num, ?_⟩
  intro k hk x hx
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · -- `k = 1`: the density is `(1/2)^{1/2} Γ(1/2)⁻¹ x^{-1/2} e^{-x/2}`, and `√x · x^{-1/2} = 1`.
    have hk1 : (k : ℝ) = 1 := by
      have : k = 1 := by omega
      rw [this]; norm_num
    rw [hk1]
    have hpdf : gammaPDFReal ((1 : ℝ) / 2) (1 / 2) x
        = ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.Gamma (1 / 2) * x ^ ((1 : ℝ) / 2 - 1)
          * Real.exp (-((1 / 2) * x)) := by
      simp only [gammaPDFReal, if_pos hx.le]
    rw [hpdf, Real.Gamma_one_half_eq]
    have hsx : Real.sqrt x * x ^ ((1 : ℝ) / 2 - 1) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      norm_num
    have hpi : (1 : ℝ) ≤ Real.sqrt π := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
    have hbase : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
    have hbase0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hexp : Real.exp (-((1 / 2) * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hexp0 : (0 : ℝ) < Real.exp (-((1 / 2) * x)) := Real.exp_pos _
    calc 2 * Real.sqrt x * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π
              * x ^ ((1 : ℝ) / 2 - 1) * Real.exp (-((1 / 2) * x)))
        = 2 * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π)
            * (Real.sqrt x * x ^ ((1 : ℝ) / 2 - 1)) * Real.exp (-((1 / 2) * x)) := by ring
      _ = 2 * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π)
            * Real.exp (-((1 / 2) * x)) := by rw [hsx, mul_one]
      _ ≤ 2 * 1 * 1 := by
          have hdiv : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          have hdiv0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) / Real.sqrt π := by positivity
          nlinarith
      _ ≤ 7 := by norm_num
  · -- `k ≥ 2`: the peak bound plus the `Γ` lower bound, both dimension-free.
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
    set a : ℝ := (k : ℝ) / 2 with hadef
    set p : ℝ := a - 1 / 2 with hpdef
    have hp : (1 : ℝ) / 2 ≤ p := by rw [hpdef, hadef]; linarith
    have hp0 : (0 : ℝ) < p := by linarith
    have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos (by rw [hadef]; linarith)
    have hpdf : gammaPDFReal a (1 / 2) x
        = ((1 : ℝ) / 2) ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-((1 / 2) * x)) := by
      simp only [gammaPDFReal, if_pos hx.le]
    have hsx : Real.sqrt x * x ^ (a - 1) = x ^ p := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      congr 1
      rw [hpdef]; ring
    have hrw : 2 * Real.sqrt x * gammaPDFReal a (1 / 2) x
        = 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * (x ^ p * Real.exp (-x / 2)) := by
      rw [hpdf, ← hsx]
      rw [show Real.exp (-((1 / 2) * x)) = Real.exp (-x / 2) by congr 1; ring]
      ring
    rw [hrw]
    have hc0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ a / Real.Gamma a := by positivity
    have hstep1 : 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * (x ^ p * Real.exp (-x / 2))
        ≤ 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * ((2 * p) ^ p * Real.exp (-p)) :=
      mul_le_mul_of_nonneg_left (rpow_mul_exp_neg_half_le hp0 hx) (by linarith)
    refine hstep1.trans ?_
    -- `(1/2)^a · 2^p = 2^{p-a} = 2^{-1/2} = (√2)⁻¹`
    have hhalf : ((1 : ℝ) / 2) ^ a * (2 : ℝ) ^ p = (Real.sqrt 2)⁻¹ := by
      have hinv : ((1 : ℝ) / 2) ^ a = ((2 : ℝ) ^ a)⁻¹ := by
        rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hinv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show -a + p = -(1 / 2) by rw [hpdef]; ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
    have hnum : 2 * (((1 : ℝ) / 2) ^ a) * ((2 * p) ^ p * Real.exp (-p))
        = 2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p)) := by
      calc 2 * (((1 : ℝ) / 2) ^ a) * ((2 * p) ^ p * Real.exp (-p))
          = 2 * ((((1 : ℝ) / 2) ^ a) * (2 : ℝ) ^ p) * (p ^ p * Real.exp (-p)) := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp0.le]; ring
        _ = 2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p)) := by rw [hhalf]
    have hgoal : 2 * (((1 : ℝ) / 2) ^ a / Real.Gamma a) * ((2 * p) ^ p * Real.exp (-p))
        = (2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p))) / Real.Gamma a := by
      rw [← hnum]; field_simp
    rw [hgoal, div_le_iff₀ hGa]
    have hGlb : p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3) ≤ Real.Gamma a := by
      have h := le_Gamma_add_half hp
      rwa [show p + 1 / 2 = a by rw [hpdef]; ring] at h
    have hq : (0 : ℝ) < p ^ p * Real.exp (-p) := by positivity
    have he3 : (0 : ℝ) < Real.exp 1 * Real.sqrt 3 := by
      have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    calc 2 * (Real.sqrt 2)⁻¹ * (p ^ p * Real.exp (-p))
        ≤ 7 * (p ^ p * Real.exp (-p) / (Real.exp 1 * Real.sqrt 3)) := by
          rw [← mul_div_assoc, le_div_iff₀ he3]
          nlinarith [mul_le_mul_of_nonneg_right peak_const_le_seven hq.le]
      _ ≤ 7 * Real.Gamma a := by linarith

/-- **Dimension-free ball (shell) anti-concentration.** There is an *absolute* constant `C`
(independent of the dimension `k`, the radius `t` and the shell width `ε`) such that the standard
multivariate Gaussian mass of the spherical shell `{t < ‖z‖ ≤ t + ε}` is at most `C · ε`. This is
the radial analogue of `gaussian_slab_measure_le` and the ingredient the ball Berry-Esseen bound
consumes. It is proved **unconditionally** (one may take `C = 7`) from the measure-theoretic
reduction `multivariateGaussian_shell_eq_chiSquared`, the elementary primitive
`integral_Ioc_inv_two_sqrt`, and the uniform chi-density peak bound
`chiSquared_density_mul_sqrt_le`. -/
theorem gaussian_ball_shell_measure_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 0 < k → ∀ t ε : ℝ, 0 ≤ t → 0 ≤ ε →
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
          {z | t < ‖z‖ ∧ ‖z‖ ≤ t + ε}).toReal ≤ C * ε := by
  obtain ⟨C, hC, hCbound⟩ := chiSquared_density_mul_sqrt_le
  refine ⟨C, hC, ?_⟩
  intro k hk t ε ht hε
  rw [multivariateGaussian_shell_eq_chiSquared hk ht hε]
  set a := t ^ 2 with ha
  set b := (t + ε) ^ 2 with hb
  have h0a : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hab : a ≤ b := by rw [ha, hb]; nlinarith
  -- Pointwise density bound `gammaPDFReal ≤ C · (2√x)⁻¹` for `x > 0`.
  have hden : ∀ x : ℝ, 0 < x →
      gammaPDFReal ((k : ℝ) / 2) (1 / 2) x ≤ C * (2 * Real.sqrt x)⁻¹ := by
    intro x hx0
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have h2 : 0 < 2 * Real.sqrt x := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h2, mul_comm]
    exact hCbound k hk x hx0
  -- Reduce the chi-squared interval mass to a Lebesgue integral of the density.
  have hcs : StatLean.MultipleTesting.chiSquared k (Set.Ioc a b)
      = ∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x := by
    unfold StatLean.MultipleTesting.chiSquared ProbabilityTheory.gammaMeasure
    rw [withDensity_apply _ measurableSet_Ioc]
  rw [hcs]
  -- Integrability and nonnegativity of the majorant `C · (2√x)⁻¹` on `(a, b]`.
  have hInt0 : IntegrableOn (fun x => (2 * Real.sqrt x)⁻¹) (Set.Ioc a b) volume := by
    have hint : IntervalIntegrable (fun x => (2 * Real.sqrt x)⁻¹) volume a b := by
      have hrpow : IntervalIntegrable (fun x => (1 / 2) * x ^ (-(1 / 2) : ℝ)) volume a b :=
        (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (1 / 2)
      refine (intervalIntegrable_congr (fun x hx => ?_)).mp hrpow
      have hx0 : 0 < x := by
        rw [Set.uIoc_of_le hab] at hx; exact lt_of_le_of_lt h0a hx.1
      rw [Real.sqrt_eq_rpow, mul_inv, Real.rpow_neg hx0.le]; ring
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hIntC : IntegrableOn (fun x => C * (2 * Real.sqrt x)⁻¹) (Set.Ioc a b) volume :=
    hInt0.const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] fun x => C * (2 * Real.sqrt x)⁻¹ :=
    ae_of_all _ fun x => mul_nonneg hC.le (by positivity)
  -- The majorant integrates to `C · ε`.
  have hmaj : ∫ x in Set.Ioc a b, C * (2 * Real.sqrt x)⁻¹ = C * ε := by
    rw [integral_const_mul, integral_Ioc_inv_two_sqrt h0a hab, hb, ha,
      Real.sqrt_sq (by linarith), Real.sqrt_sq ht]; ring
  -- Bound the lintegral by `ofReal (C · ε)`.
  have hlint : ∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x
      ≤ ENNReal.ofReal (C * ε) := by
    calc ∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x
        ≤ ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (C * (2 * Real.sqrt x)⁻¹) := by
          apply setLIntegral_mono_ae (by fun_prop)
          refine ae_of_all _ (fun x hx => ?_)
          have hx0 : 0 < x := lt_of_le_of_lt h0a hx.1
          rw [show gammaPDF ((k : ℝ) / 2) (1 / 2) x
              = ENNReal.ofReal (gammaPDFReal ((k : ℝ) / 2) (1 / 2) x) from rfl]
          exact ENNReal.ofReal_le_ofReal (hden x hx0)
      _ = ENNReal.ofReal (∫ x in Set.Ioc a b, C * (2 * Real.sqrt x)⁻¹) :=
          (ofReal_integral_eq_lintegral_ofReal hIntC hnn).symm
      _ = ENNReal.ofReal (C * ε) := by rw [hmaj]
  calc (∫⁻ x in Set.Ioc a b, gammaPDF ((k : ℝ) / 2) (1 / 2) x).toReal
      ≤ (ENNReal.ofReal (C * ε)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = C * ε := ENNReal.toReal_ofReal (mul_nonneg hC.le hε)

end BallAntiConcentration

/-! ### The remaining ingredients of the elementary route

Of the analytic bricks of the Lindeberg-swap route, the third-order Taylor remainder
(`norm_taylor_remainder_three_le`) and — for the **ball** route — the smoothed radial
indicator (`exists_smoothed_radial_indicator`) are now proved here, unconditionally and with
dimension-free constants. The **multivariate Lindeberg swap** `abs_integral_smooth_sub_gaussian_le`
and — for the *convex* route — `exists_smoothed_convex_indicator` are proved here as well, so no
brick of the route is left as debt. The honest final bounds
`berryEsseen_ball_elementary` / `berryEsseen_convex_elementary` record the exact statements the
route delivers; their exponent `(β/√n)^{1/4}` is the genuine — non-sharp — outcome (see the
module docstring). -/

section ElementaryRoute

/-- **Third-order Taylor remainder on a normed space.** For `C³` `f` with `‖D³f‖ ≤ M`, the
second-order Taylor error at `x` in direction `h` is at most `M ‖h‖³ / 6`. This is the analytic
heart of the Lindeberg swap. Mathlib v4.29.1 has only the one-dimensional Taylor remainder, so we
reduce to the segment `t ↦ f (x + t • h)` (a `C³` map `ℝ → ℝ`), apply the 1-D Lagrange bound, and
identify `(d/dt)ᵐ f(x+t•h) = iteratedFDeriv ℝ m f (x+t•h) (fun _ => h)` via the composition of the
translation `w ↦ f (x + w)` with the continuous linear map `t ↦ t • h`. -/
private lemma norm_taylor_remainder_three_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ}
    (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) (x h : E) :
    |f (x + h) - f x - fderiv ℝ f x h - (1 / 2) * iteratedFDeriv ℝ 2 f x (fun _ => h)|
      ≤ M / 6 * ‖h‖ ^ 3 := by
  -- The line restriction `g s = f (x + s • h)`.
  set g : ℝ → ℝ := fun s => f (x + s • h) with hg
  -- The continuous linear map `L : t ↦ t • h`, so that `g = (fun w => f (x + w)) ∘ L`.
  set L : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight h with hLdef
  have hLapp : ∀ t : ℝ, L t = t • h := by
    intro t
    simp only [hLdef, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
  have hF : ContDiff ℝ 3 (fun w : E => f (x + w)) := hf.comp (contDiff_const.add contDiff_id)
  -- Core identity: `(d/ds)ᵐ g = iteratedFDeriv ℝ m f (x + s•h) (fun _ => h)` for `m ≤ 3`.
  have key : ∀ (m : ℕ), m ≤ 3 → ∀ s : ℝ,
      iteratedDeriv m g s = iteratedFDeriv ℝ m f (x + s • h) (fun _ => h) := by
    intro m hm s
    have hcomp : g = (fun w : E => f (x + w)) ∘ L := by funext t; simp [hg, hLapp]
    rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
      ContinuousLinearMap.iteratedFDeriv_comp_right L hF s (by exact_mod_cast hm),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
    rw [hLapp]
    congr 1
    funext i; rw [hLapp]; simp
  -- `g` is `C³`, hence `C³` on `[0,1]`.
  have hgcd : ContDiff ℝ 3 g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgcdOn : ContDiffOn ℝ 3 g (Set.Icc 0 1) := hgcd.contDiffOn
  -- 1-D Lagrange remainder of order 2 on `[0,1]` (so the remainder is `g'''(x')/6`).
  obtain ⟨x', _hx', heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (by norm_num : (0 : ℝ) < 1)
      (by exact_mod_cast hgcdOn)
  -- Convert `iteratedDerivWithin k g (Icc 0 1) 0` to the multilinear derivative of `f` at `x`.
  have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hidw : ∀ k, k ≤ 3 →
      iteratedDerivWithin k g (Set.Icc 0 1) 0 = iteratedFDeriv ℝ k f x (fun _ => h) := by
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
        (hgcd.contDiffAt.of_le (by exact_mod_cast hk)) hmem, key k hk 0]
    simp
  -- Expand the Taylor polynomial into the three visible terms.
  have htaylor : taylorWithinEval g 2 (Set.Icc 0 1) 0 1
      = f x + fderiv ℝ f x h + (1 / 2) * iteratedFDeriv ℝ 2 f x (fun _ => h) := by
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      hidw 0 (by norm_num), hidw 1 (by norm_num), hidw 2 (by norm_num),
      iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
    norm_num [Nat.factorial, smul_eq_mul]
  -- Bound the third-order term.
  have hb3 : |iteratedDeriv 3 g x'| ≤ M * ‖h‖ ^ 3 := by
    rw [key 3 le_rfl x', ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 3 f (x + x' • h) (fun _ => h)‖
        ≤ ‖iteratedFDeriv ℝ 3 f (x + x' • h)‖ * ∏ _i : Fin 3, ‖h‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 3 f (x + x' • h)‖ * ‖h‖ ^ 3 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ M * ‖h‖ ^ 3 := by gcongr; exact hM _
  -- Assemble.
  have hg1 : g 1 = f (x + h) := by simp [hg]
  have hrw : f (x + h) - f x - fderiv ℝ f x h - (1 / 2) * iteratedFDeriv ℝ 2 f x (fun _ => h)
      = g 1 - taylorWithinEval g 2 (Set.Icc 0 1) 0 1 := by rw [hg1, htaylor]; ring
  rw [hrw, heq]
  have hfact : (Nat.factorial (2 + 1) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfact, show ((1 : ℝ) - 0) ^ 3 = 1 by norm_num, mul_one, abs_div,
    show |(6 : ℝ)| = 6 by norm_num]
  calc |iteratedDeriv 3 g x'| / 6 ≤ M * ‖h‖ ^ 3 / 6 := by gcongr
    _ = M / 6 * ‖h‖ ^ 3 := by ring

/-! #### The smoothed indicator of an arbitrary set (mollification)

This block pays what the wave-4 note called the "`precompR` bookkeeping" debt: it constructs,
for an arbitrary set `B ⊆ ℝ^k` and an arbitrary width `ε > 0`, a `C³` function `f : ℝ^k → [0,1]`
that is `1` on `B`, vanishes outside the `ε`-thickening of `B`, and satisfies
`‖D³f‖ ≤ C₃(k)/ε³` with `C₃(k)` fixed *before* `B` and `ε`.

The construction is the mollification predicted by the note, with one simplification that
removes its most delicate step. Rather than rescaling the `ContDiffBump` kernel with `ε` (which
would require the `δ`-dilation identity for `ContDiffBump` together with the Haar change of
variables `∫ g(δ·) = δ^{-k} ∫ g`), we build the width-`1` object once and obtain the width-`ε`
object by **dilating the set**: applying the width-`1` construction to `ε⁻¹ • B` and
precomposing with the continuous linear map `x ↦ ε⁻¹ • x`. All the `ε`-dependence then comes
from `ContinuousLinearMap.iteratedFDeriv_comp_right` together with
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`, i.e. from `‖L‖³ ≤ ε⁻³`; no measure
rescaling is needed anywhere.

At width `1` the construction is: mollify the indicator of `Metric.thickening (1/2) B` with the
normed bump of radii `1/8 < 1/4`. The support clause holds because `1/2 + 1/4 < 1`, the value
clause because the whole mass of the kernel sits inside the thickening when `x ∈ B`, and
`0 ≤ f ≤ 1` because the kernel is a probability density.

For the third derivative we use the only differentiation formula Mathlib v4.29.1 has for
convolutions, the first-order `HasCompactSupport.hasFDerivAt_convolution_right`, three times;
the resulting tower `L`, `L.precompR`, `L.precompR.precompR` is glued to `iteratedFDeriv` by
three applications of `norm_iteratedFDeriv_fderiv`, exactly as the wave-4 note predicted. The
`precompR` tower costs nothing quantitatively because `‖L.precompR E‖ ≤ ‖L‖`
(`ContinuousLinearMap.norm_precompR_le`) and `‖lsmul ℝ ℝ‖ ≤ 1`, so the bound is simply
`‖D³f‖ ≤ ∫ ‖D³φ‖` for the fixed kernel `φ`.

Note that **convexity of `B` is never used**: the mollification works for any set. Convexity is
needed only for the *other* convex ingredient, the boundary-shell bound `γ(Bᵋ \ B) ≤ C_k ε`,
which lives in `StatLean.HypothesisTesting.ForMathlib.GaussianShell`
(`gaussian_thickening_le`; see `berryEsseen_convex_elementary` for the assembly). -/

section ConvexSmoothing

open Metric

open scoped Convolution Pointwise

/-- The fixed mollification kernel: the `ContDiffBump` at the origin with radii `1/8 < 1/4`. -/
private noncomputable def mbeBump (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin k)) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The normed mollification kernel: smooth, nonnegative, supported in the ball of radius `1/4`
and of total mass `1`. -/
private noncomputable def mbeMollifier (k : ℕ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  (mbeBump k).normed volume

private lemma mbeMollifier_nonneg (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    0 ≤ mbeMollifier k x :=
  ContDiffBump.nonneg_normed (mbeBump k) x

private lemma mbeMollifier_contDiff (k : ℕ) :
    ContDiff ℝ (((4 : ℕ∞) : WithTop ℕ∞)) (mbeMollifier k) :=
  ContDiffBump.contDiff_normed (mbeBump k)

private lemma mbeMollifier_hasCompactSupport (k : ℕ) : HasCompactSupport (mbeMollifier k) :=
  ContDiffBump.hasCompactSupport_normed (mbeBump k)

private lemma mbeMollifier_integral (k : ℕ) : ∫ x, mbeMollifier k x = 1 :=
  ContDiffBump.integral_normed (mbeBump k)

private lemma mbeMollifier_integrable (k : ℕ) : Integrable (mbeMollifier k) :=
  ContDiffBump.integrable_normed (mbeBump k)

private lemma mbeMollifier_support (k : ℕ) :
    Function.support (mbeMollifier k) = ball 0 (1 / 4) := by
  rw [mbeMollifier, ContDiffBump.support_normed_eq]; rfl

section GenericConvolutionBound

variable {G E' F : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

/-- If the pairing has operator norm `≤ 1` and `ind` is bounded by `1` in absolute value, then
the convolution `ind ⋆[L] g` is bounded by the `L¹`-norm of `g`. This is the quantitative half
of the mollification bound, stated abstractly so that the elaborator never has to see the
concrete `precompR` tower. -/
private lemma norm_convolution_le_of_bounded (L : ℝ →L[ℝ] E' →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {ind : G → ℝ} (hbd : ∀ t, |ind t| ≤ 1) {g : G → E'} (hg : Integrable g μ) (x : G) :
    ‖(ind ⋆[L, μ] g) x‖ ≤ ∫ t, ‖g t‖ ∂μ := by
  have hint : Integrable (fun t => ‖g t‖) μ := hg.norm
  calc ‖(ind ⋆[L, μ] g) x‖ = ‖∫ t, L (ind t) (g (x - t)) ∂μ‖ := by rw [convolution_def]
    _ ≤ ∫ t, ‖L (ind t) (g (x - t))‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖g (x - t)‖ ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hint.comp_sub_left x) (Filter.Eventually.of_forall fun t => ?_)
        refine (L.le_opNorm₂ (ind t) (g (x - t))).trans ?_
        have h1 : ‖ind t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hbd t
        have h2 : ‖L‖ * ‖ind t‖ ≤ 1 := mul_le_one₀ hL (norm_nonneg _) h1
        calc ‖L‖ * ‖ind t‖ * ‖g (x - t)‖ ≤ 1 * ‖g (x - t)‖ := by gcongr
          _ = ‖g (x - t)‖ := one_mul _
    _ = ∫ t, ‖g t‖ ∂μ := integral_sub_left_eq_self (fun t => ‖g t‖) μ x

end GenericConvolutionBound

set_option maxHeartbeats 1000000 in
-- The `precompR` tower forces defeq checks on the continuous-linear-map type
-- `ℝ →L (E →L E →L E →L ℝ) →L (E →L E →L E →L ℝ)`; those are what exhaust the default budget.
/-- The third derivative of a mollification is bounded by the `L¹`-norm of the third derivative
of the kernel, uniformly over all `ind` bounded by `1`.

This is the `precompR` tower: three applications of
`HasCompactSupport.hasFDerivAt_convolution_right`
identify `fderiv³ (ind ⋆ φ)` with `ind ⋆[L₃] fderiv³ φ`, and three applications of
`norm_iteratedFDeriv_fderiv` turn `‖iteratedFDeriv ℝ 3 ·‖` into `‖fderiv³ ·‖`.

The raised heartbeat budget pays for the defeq checks on the continuous-linear-map tower
`ℝ →L (E →L E →L E →L ℝ) →L (E →L E →L E →L ℝ)`; the proof itself is three rewrites and a
bound. -/
private lemma norm_iteratedFDeriv_three_convolution_le {k : ℕ}
    {ind : EuclideanSpace ℝ (Fin k) → ℝ} (hind : LocallyIntegrable ind volume)
    (hbd : ∀ t, |ind t| ≤ 1) (x : EuclideanSpace ℝ (Fin k)) :
    ‖iteratedFDeriv ℝ 3 (ind ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mbeMollifier k) x‖
      ≤ ∫ t, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (mbeMollifier k))) t‖ := by
  set φ := mbeMollifier k with hφdef
  have hφ : ContDiff ℝ (((4 : ℕ∞) : WithTop ℕ∞)) φ := mbeMollifier_contDiff k
  have hcs : HasCompactSupport φ := mbeMollifier_hasCompactSupport k
  set L₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL₀
  set L₁ := L₀.precompR (EuclideanSpace ℝ (Fin k)) with hL₁
  set L₂ := L₁.precompR (EuclideanSpace ℝ (Fin k)) with hL₂
  set L₃ := L₂.precompR (EuclideanSpace ℝ (Fin k)) with hL₃
  set φ₁ := fderiv ℝ φ with hφ₁
  set φ₂ := fderiv ℝ φ₁ with hφ₂
  set φ₃ := fderiv ℝ φ₂ with hφ₃
  have hφ1 : ContDiff ℝ (((3 : ℕ∞) : WithTop ℕ∞)) φ₁ := hφ.fderiv_right (by norm_num)
  have hφ2 : ContDiff ℝ (((2 : ℕ∞) : WithTop ℕ∞)) φ₂ := hφ1.fderiv_right (by norm_num)
  have hφ3 : ContDiff ℝ (((1 : ℕ∞) : WithTop ℕ∞)) φ₃ := hφ2.fderiv_right (by norm_num)
  have hcs1 : HasCompactSupport φ₁ := hcs.fderiv ℝ
  have hcs2 : HasCompactSupport φ₂ := hcs1.fderiv ℝ
  have hcs3 : HasCompactSupport φ₃ := hcs2.fderiv ℝ
  have hd1 : fderiv ℝ (ind ⋆[L₀, volume] φ) = (ind ⋆[L₁, volume] φ₁) := by
    funext y
    exact (hcs.hasFDerivAt_convolution_right L₀ hind (hφ.of_le (by norm_num)) y).fderiv
  have hd2 : fderiv ℝ (ind ⋆[L₁, volume] φ₁) = (ind ⋆[L₂, volume] φ₂) := by
    funext y
    exact (hcs1.hasFDerivAt_convolution_right L₁ hind (hφ1.of_le (by norm_num)) y).fderiv
  have hd3 : fderiv ℝ (ind ⋆[L₂, volume] φ₂) = (ind ⋆[L₃, volume] φ₃) := by
    funext y
    exact (hcs2.hasFDerivAt_convolution_right L₂ hind (hφ2.of_le (by norm_num)) y).fderiv
  have hkey : ‖iteratedFDeriv ℝ 3 (ind ⋆[L₀, volume] φ) x‖ = ‖(ind ⋆[L₃, volume] φ₃) x‖ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd1,
      show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd2,
      show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hd3]
    simp [norm_iteratedFDeriv_zero]
  rw [hkey]
  have hnormL : ‖L₃‖ ≤ 1 := by
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₂) ?_
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₁) ?_
    refine le_trans (ContinuousLinearMap.norm_precompR_le _ L₀) ?_
    exact ContinuousLinearMap.opNorm_lsmul_le
  exact norm_convolution_le_of_bounded L₃ hnormL hbd
    (hφ3.continuous.integrable_of_hasCompactSupport hcs3) x

/-- **Smoothed indicator at unit width, for an arbitrary set.** There is a constant `C₃`
(depending only on the dimension `k`, and fixed *before* the set) such that every
`B ⊆ ℝ^k` admits a `C³` function `f : ℝ^k → [0,1]` equal to `1` on `B`, supported inside the
unit thickening of `B`, with `‖D³f‖ ≤ C₃`.

Take `f` to be the mollification of the indicator of `Metric.thickening (1/2) B` by
`mbeMollifier k`. Note the empty set needs no special treatment: then `f = 0` and both the
value and the support clause are vacuous. -/
private lemma exists_smoothed_indicator_unit (k : ℕ) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ B : Set (EuclideanSpace ℝ (Fin k)),
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x ∈ B, f x = 1) ∧ (∀ x, f x ≠ 0 → x ∈ thickening 1 B) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃) := by
  set φ := mbeMollifier k with hφdef
  refine ⟨max 1 (∫ t, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) t‖),
    lt_of_lt_of_le one_pos (le_max_left _ _), fun B => ?_⟩
  set A : Set (EuclideanSpace ℝ (Fin k)) := thickening (1 / 2) B with hAdef
  set ind : EuclideanSpace ℝ (Fin k) → ℝ := A.indicator (fun _ => (1 : ℝ)) with hinddef
  have hindmeas : Measurable ind := measurable_const.indicator isOpen_thickening.measurableSet
  have hindbd : ∀ t, |ind t| ≤ 1 := by
    intro t
    have := norm_indicator_le_norm_self (fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ)) (s := A) t
    simpa [hinddef] using this
  have hindnn : ∀ t, 0 ≤ ind t := fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hindle : ∀ t, ind t ≤ 1 := fun t => (abs_le.1 (hindbd t)).2
  have hind : LocallyIntegrable ind volume :=
    (locallyIntegrable_const (1 : ℝ)).mono hindmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => norm_indicator_le_norm_self _ t)
  set L₀ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL₀
  -- the value of the mollification, with the kernel carrying the free variable
  have hval : ∀ x, (ind ⋆[L₀, volume] φ) x = ∫ t, ind (x - t) * φ t := by
    intro x
    rw [convolution_eq_swap]
    simp [hL₀, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hsupp : ∀ t : EuclideanSpace ℝ (Fin k), φ t ≠ 0 → ‖t‖ < 1 / 4 := by
    intro t ht
    have hmem : t ∈ Function.support φ := ht
    rw [hφdef, mbeMollifier_support] at hmem
    simpa [dist_zero_right] using hmem
  refine ⟨ind ⋆[L₀, volume] φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mbeMollifier_hasCompactSupport k).contDiff_convolution_right L₀ hind
      ((mbeMollifier_contDiff k).of_le (by norm_num))
  · intro x
    rw [hval]
    exact integral_nonneg fun t => mul_nonneg (hindnn _) (mbeMollifier_nonneg k t)
  · intro x
    rw [hval]
    refine le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => mul_nonneg (hindnn _) (mbeMollifier_nonneg k t))
      (mbeMollifier_integrable k) (Filter.Eventually.of_forall fun t => ?_)) ?_
    · nlinarith [hindle (x - t), hindnn (x - t), mbeMollifier_nonneg k t]
    · exact le_of_eq (mbeMollifier_integral k)
  · -- on `B` the whole mass of the kernel sits inside the `1/2`-thickening
    intro x hx
    rw [hval]
    have hpt : ∀ t, ind (x - t) * φ t = φ t := by
      intro t
      rcases eq_or_ne (φ t) 0 with h | h
      · simp [h]
      · have hmem : x - t ∈ A := by
          rw [hAdef, Metric.mem_thickening_iff]
          refine ⟨x, hx, ?_⟩
          have hd : dist (x - t) x = ‖t‖ := by rw [dist_eq_norm]; simp [norm_neg]
          rw [hd]
          exact lt_trans (hsupp t h) (by norm_num)
        rw [hinddef, Set.indicator_of_mem hmem]
        ring
    simp only [hpt]
    exact mbeMollifier_integral k
  · -- off the unit thickening the integrand vanishes identically, since `1/2 + 1/4 < 1`
    intro x hfx
    by_contra hx
    apply hfx
    rw [hval]
    have hpt : ∀ t, ind (x - t) * φ t = 0 := by
      intro t
      rcases eq_or_ne (φ t) 0 with h | h
      · simp [h]
      · have hnot : x - t ∉ A := by
          intro hmem
          rw [hAdef, Metric.mem_thickening_iff] at hmem
          obtain ⟨z, hz, hdz⟩ := hmem
          apply hx
          rw [Metric.mem_thickening_iff]
          refine ⟨z, hz, ?_⟩
          have h1 : dist x (x - t) = ‖t‖ := by rw [dist_eq_norm]; simp
          have h3 := dist_triangle x (x - t) z
          have h2 := hsupp t h
          linarith
        rw [hinddef, Set.indicator_of_notMem hnot]
        ring
    simp only [hpt]
    exact integral_zero _ _
  · intro x
    exact le_trans (norm_iteratedFDeriv_three_convolution_le hind hindbd x) (le_max_right 1 _)

/-- **Smoothed convex indicator with controlled third derivative.**
In each dimension `k` there is a constant `C₃` (quantified *before* `B` and `ε`, so the bound
is not vacuous) such that every convex `B` and width `ε > 0` admit a smooth `f : ℝ^k → [0,1]`
equal to `1` on `B`, supported inside the `ε`-thickening of `B`, with `‖D³f‖ ≤ C₃ / ε³`.

**Proof.** Apply `exists_smoothed_indicator_unit` to the dilate `ε⁻¹ • B` and precompose with
the continuous linear map `L : x ↦ ε⁻¹ • x`. Membership and support transport along `L` because
`dist (ε⁻¹ • x) (ε⁻¹ • w) = ε⁻¹ * dist x w`, and the derivative bound transports by
`ContinuousLinearMap.iteratedFDeriv_comp_right` together with
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`, which contribute the factor
`‖L‖³ ≤ ε⁻³`. Note `‖L‖ ≤ ε⁻¹` is used as an inequality rather than an equality, so the
degenerate dimension `k = 0` (where `‖id‖ = 0`) is covered too.

Convexity of `B` is not used; it is kept only because the statement is frozen. -/
private lemma exists_smoothed_convex_indicator (k : ℕ) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ B : Set (EuclideanSpace ℝ (Fin k)), Convex ℝ B → ∀ {ε : ℝ}, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x ∈ B, f x = 1) ∧ (∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := exists_smoothed_indicator_unit k
  refine ⟨C₃, hC₃pos, fun B _ ε hε => ?_⟩
  obtain ⟨g, hgcd, hg0, hg1, hgB, hgsupp, hgD⟩ := hC₃ (ε⁻¹ • B)
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ε⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) with hLdef
  have hLapp : ∀ x, L x = ε⁻¹ • x := by intro x; simp [hLdef]
  have hLnorm : ‖L‖ ≤ ε⁻¹ := by
    rw [hLdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hid : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have hεinv : (0 : ℝ) ≤ ε⁻¹ := by positivity
    nlinarith [hid, hεinv]
  refine ⟨fun x => g (L x), hgcd.comp L.contDiff, fun x => hg0 _, fun x => hg1 _, ?_, ?_, ?_⟩
  · intro x hx
    exact hgB _ (by rw [hLapp]; exact Set.smul_mem_smul_set hx)
  · intro x hx
    have hmem := hgsupp _ hx
    rw [Metric.mem_thickening_iff] at hmem ⊢
    obtain ⟨z, hz, hdz⟩ := hmem
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, hw, ?_⟩
    rw [hLapp, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ε⁻¹)] at hdz
    rw [dist_eq_norm]
    rw [inv_mul_lt_iff₀ hε] at hdz
    linarith
  · intro x
    have hcomp : (fun x => g (L x)) = g ∘ L := rfl
    rw [hcomp, L.iteratedFDeriv_comp_right hgcd x (le_refl _)]
    refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
    have hprod : (∏ _i : Fin 3, ‖L‖) = ‖L‖ ^ 3 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod]
    calc ‖iteratedFDeriv ℝ 3 g (L x)‖ * ‖L‖ ^ 3 ≤ C₃ * ε⁻¹ ^ 3 := by
          gcongr
          exact hgD _
      _ = C₃ / ε ^ 3 := by rw [inv_pow]; ring

end ConvexSmoothing

/-! #### The smoothed radial indicator

The construction composes a **fixed** one-dimensional cutoff with the *squared* norm `‖·‖²`
rather than with `‖·‖`. This is what makes the third-derivative constant genuinely
dimension-free *and* elementary: `‖·‖²` is a quadratic polynomial, so `D¹‖·‖² = 2⟪z,·⟫`,
`D²‖·‖² = 2⟪·,·⟫` and `D³‖·‖² = 0`, with dimension-free norms `2‖z‖`, `2`, `0` — all obtained
from Mathlib's bilinear iterated-derivative bound applied to `innerSL ℝ`. In particular the
quantitative iterated-derivative bounds for `‖·‖` away from the origin (which Mathlib v4.29.1
does not provide, and which the `χ ∘ ‖·‖` route would need) are never used. -/

section RadialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed one-dimensional cutoff `χ = 1 - smoothTransition`: smooth, equal to `1` on
`(-∞, 0]`, to `0` on `[1, ∞)`, with values in `[0,1]`. -/
private noncomputable def radialCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

private lemma contDiff_radialCutoff : ContDiff ℝ 3 radialCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

private lemma radialCutoff_nonneg (t : ℝ) : 0 ≤ radialCutoff t :=
  sub_nonneg.mpr (Real.smoothTransition.le_one t)

private lemma radialCutoff_le_one (t : ℝ) : radialCutoff t ≤ 1 := by
  have := Real.smoothTransition.nonneg t
  simp only [radialCutoff]; linarith

private lemma radialCutoff_of_nonpos {t : ℝ} (h : t ≤ 0) : radialCutoff t = 1 := by
  simp [radialCutoff, Real.smoothTransition.zero_of_nonpos h]

private lemma radialCutoff_of_one_le {t : ℝ} (h : 1 ≤ t) : radialCutoff t = 0 := by
  simp [radialCutoff, Real.smoothTransition.one_of_one_le h]

/-- The derivatives of the fixed cutoff are bounded on the transition window `[0,1]` by an
absolute constant `B ≥ 1` (continuity on a compact). Off `[0,1]` the cutoff is locally
constant, so this is all that is ever needed. -/
private lemma exists_radialCutoff_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ 3, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i radialCutoff t‖ ≤ B := by
  have hc : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ 3 →
      ContinuousOn (iteratedFDeriv ℝ i radialCutoff) (Set.Icc (0 : ℝ) 1) := fun i hi =>
    (contDiff_radialCutoff.continuous_iteratedFDeriv hi).continuousOn
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 0 (by norm_num))
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 1 (by norm_num))
  obtain ⟨B2, hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 2 (by norm_num))
  obtain ⟨B3, hB3⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 3 (by norm_num))
  refine ⟨max 1 (max B0 (max B1 (max B2 B3))), le_max_left _ _, ?_⟩
  intro i hi t ht
  interval_cases i
  · exact (hB0 t ht).trans (by simp)
  · exact (hB1 t ht).trans (by simp)
  · exact (hB2 t ht).trans (by simp)
  · exact (hB3 t ht).trans (by simp)

/-! ##### Iterated derivatives of the squared norm (dimension-free) -/

private lemma norm_iteratedFDeriv_id_one_le (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y : E => y) x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one, fderiv_id']
  exact ContinuousLinearMap.norm_id_le

private lemma norm_iteratedFDeriv_id_of_two_le {i : ℕ} (hi : 2 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have h : (fderiv ℝ fun y : E => y) = fun _ : E => ContinuousLinearMap.id ℝ E := by
    funext y; exact fderiv_id'
  rw [h, iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0)]
  simp

/-- Mathlib's bilinear iterated-derivative bound applied to `‖y‖² = ⟪y, y⟫`. -/
private lemma norm_iteratedFDeriv_normSq_le (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y : E => ‖y‖ ^ 2) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (fun y : E => y) x‖
          * ‖iteratedFDeriv ℝ (n - i) (fun y : E => y) x‖ := by
  have hfun : (fun y : E => ‖y‖ ^ 2)
      = fun y : E => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y y := by
    funext y
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [hfun]
  exact ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _
    (contDiff_id (n := (n : WithTop ℕ∞))) (contDiff_id (n := (n : WithTop ℕ∞))) x le_rfl
    (norm_innerSL_le ℝ)

private lemma norm_iteratedFDeriv_normSq_one (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 2 * ‖x‖ := by
  refine (norm_iteratedFDeriv_normSq_le 1 x).trans ?_
  have h1 := norm_iteratedFDeriv_id_one_le x
  have h0 : ‖iteratedFDeriv ℝ 0 (fun y : E => y) x‖ = ‖x‖ := norm_iteratedFDeriv_zero
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
    one_mul, h0]
  nlinarith [h1, hx]

private lemma norm_iteratedFDeriv_normSq_two (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 2 := by
  refine (norm_iteratedFDeriv_normSq_le 2 x).trans ?_
  have h1 := norm_iteratedFDeriv_id_one_le x
  have h2 : ‖iteratedFDeriv ℝ 2 (fun y : E => y) x‖ = 0 :=
    norm_iteratedFDeriv_id_of_two_le le_rfl x
  have h0 : ‖iteratedFDeriv ℝ 0 (fun y : E => y) x‖ = ‖x‖ := norm_iteratedFDeriv_zero
  have hn1 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ 1 (fun y : E => y) x‖ := norm_nonneg _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, one_mul, h0, h2, mul_zero, zero_mul,
    zero_add, add_zero]
  nlinarith [h1, hn1]

private lemma norm_iteratedFDeriv_normSq_three (x : E) :
    ‖iteratedFDeriv ℝ 3 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 0 := by
  refine (norm_iteratedFDeriv_normSq_le 3 x).trans ?_
  have h2 : ‖iteratedFDeriv ℝ 2 (fun y : E => y) x‖ = 0 :=
    norm_iteratedFDeriv_id_of_two_le le_rfl x
  have h3 : ‖iteratedFDeriv ℝ 3 (fun y : E => y) x‖ = 0 :=
    norm_iteratedFDeriv_id_of_two_le (by norm_num) x
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, h2, h3, mul_zero, zero_mul, add_zero]
  exact le_rfl

end RadialSmoothing

/-- **Smoothed radial indicator with an absolute (dimension-free) third-derivative constant.**
There is a constant `C₃` — independent of the dimension `k`, the radius `a` and the width `ε` —
such that for every ball `{‖z‖ ≤ a}` with `0 ≤ a` and every width `ε > 0` there is a smooth
`f : ℝ^k → [0,1]`, equal to `1` on `{‖z‖ ≤ a}`, vanishing on `{‖z‖ > a + ε}`, with
`‖D³f‖ ≤ C₃ / ε³`. This is the radial analogue of `exists_smoothed_convex_indicator`, and unlike
the convex one its constant is genuinely dimension-free.

**Construction.** `f = χ(( ‖·‖² − a²)/W)` with `W = (a+ε)² − a² = ε(2a+ε)` and `χ` the *fixed*
cutoff `radialCutoff` (`1` on `(-∞,0]`, `0` on `[1,∞)`). Composing with `‖·‖²` rather than with
`‖·‖` is essential: `‖·‖²` is a quadratic polynomial, hence globally smooth (no singularity at
the origin) with `‖D¹‖·‖²‖ = 2‖z‖`, `‖D²‖·‖²‖ ≤ 2`, `D³‖·‖² = 0`, all dimension-free.

**Third-derivative bound.** Write `u = ‖·‖²/W`, so `f = χ(· − a²/W) ∘ u`. On the transition
shell `a ≤ ‖z‖ ≤ a+ε` one has `‖D¹u‖ = 2‖z‖/W ≤ 2(a+ε)/(ε(2a+ε)) ≤ 2/ε` and
`‖D²u‖ = 2/W ≤ 4/ε² = (2/ε)²`, while `D³u = 0`; so `‖Dⁱu‖ ≤ D^i` with the *single* geometric
ratio `D = 2/ε`, and Mathlib's `norm_iteratedFDeriv_comp_le` gives
`‖D³f‖ ≤ 3! · B · (2/ε)³ = 48B/ε³` with `B` the absolute bound of `exists_radialCutoff_bound`.
Off that shell `f` is locally constant, so `D³f = 0`.

Note the hypothesis `ε ≤ a` of the earlier `χ ∘ ‖·‖` formulation is **not** needed here: the
squared-norm route is uniform down to `a = 0`. -/
private lemma exists_smoothed_radial_indicator :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (k : ℕ) (a : ℝ), 0 ≤ a → ∀ {ε : ℝ}, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a → f x = 1) ∧ (∀ x, a + ε < ‖x‖ → f x = 0) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) := by
  obtain ⟨B, hB1, hB⟩ := exists_radialCutoff_bound
  refine ⟨48 * B, by linarith, ?_⟩
  intro k a ha ε hε
  set W : ℝ := 2 * a * ε + ε ^ 2 with hWdef
  have hW0 : 0 < W := by rw [hWdef]; nlinarith
  set c : ℝ := a ^ 2 / W with hcdef
  set u : EuclideanSpace ℝ (Fin k) → ℝ := fun y => W⁻¹ • ‖y‖ ^ 2 with hudef
  set g : ℝ → ℝ := fun t => radialCutoff (-c + t) with hgdef
  have huCD : ContDiff ℝ 3 u := (contDiff_norm_sq ℝ).const_smul W⁻¹
  have hgCD : ContDiff ℝ 3 g :=
    contDiff_radialCutoff.comp (contDiff_const.add contDiff_id)
  -- `g (u y) = χ((‖y‖² − a²)/W)`
  have hval : ∀ y : EuclideanSpace ℝ (Fin k),
      (g ∘ u) y = radialCutoff ((‖y‖ ^ 2 - a ^ 2) / W) := by
    intro y
    simp only [Function.comp_apply, hgdef, hudef, hcdef, smul_eq_mul]
    congr 1
    field_simp
    try ring
  refine ⟨g ∘ u, hgCD.comp huCD, fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x => ?_⟩
  · rw [hval]; exact radialCutoff_nonneg _
  · rw [hval]; exact radialCutoff_le_one _
  · rw [hval]
    refine radialCutoff_of_nonpos ?_
    apply div_nonpos_of_nonpos_of_nonneg _ hW0.le
    have : ‖x‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg x]
    linarith
  · rw [hval]
    refine radialCutoff_of_one_le ?_
    rw [le_div_iff₀ hW0]
    have hxa : a + ε < ‖x‖ := hx
    nlinarith [norm_nonneg x]
  · -- the third-derivative bound
    set v : ℝ := (‖x‖ ^ 2 - a ^ 2) / W with hvdef
    by_cases hcase : 0 ≤ v ∧ v ≤ 1
    · -- transition shell: Faà di Bruno with the geometric ratio `D = 2/ε`
      obtain ⟨hv0, hv1⟩ := hcase
      have hxle : ‖x‖ ≤ a + ε := by
        rw [hvdef, div_le_one hW0] at hv1
        nlinarith [norm_nonneg x]
      have hCb : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g (u x)‖ ≤ B := by
        intro i hi
        have hshift : iteratedFDeriv ℝ i g = fun t => iteratedFDeriv ℝ i radialCutoff (-c + t) :=
          iteratedFDeriv_comp_add_left' i (-c)
        have harg : -c + u x = v := by
          simp only [hudef, hcdef, hvdef, smul_eq_mul]
          field_simp
          try ring
        rw [hshift]
        change ‖iteratedFDeriv ℝ i radialCutoff (-c + u x)‖ ≤ B
        rw [harg]
        exact hB i hi v ⟨hv0, hv1⟩
      have hD : ∀ i, 1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i u x‖ ≤ (2 / ε) ^ i := by
        intro i _ hi3
        have hsc : iteratedFDeriv ℝ i u x
            = W⁻¹ • iteratedFDeriv ℝ i (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) x :=
          iteratedFDeriv_const_smul_apply' ((contDiff_norm_sq ℝ).contDiffAt)
        rw [hsc, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW0)]
        interval_cases i
        · rw [pow_one, inv_mul_le_iff₀ hW0]
          have hWid : W * (2 / ε) = 2 * (2 * a + ε) := by
            rw [hWdef]; field_simp; try ring
          rw [hWid]
          have h := norm_iteratedFDeriv_normSq_one x
          nlinarith [h, hxle, ha, norm_nonneg x]
        · rw [inv_mul_le_iff₀ hW0]
          have hWid : W * (2 / ε) ^ 2 = 4 * (2 * a + ε) / ε := by
            rw [hWdef]; field_simp; try ring
          rw [hWid]
          have h := norm_iteratedFDeriv_normSq_two x
          have h2 : (2 : ℝ) ≤ 4 * (2 * a + ε) / ε := by
            rw [le_div_iff₀ hε]; nlinarith
          linarith
        · rw [inv_mul_le_iff₀ hW0]
          have h := norm_iteratedFDeriv_normSq_three x
          have hz : ‖iteratedFDeriv ℝ 3
              (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) x‖ = 0 :=
            le_antisymm h (norm_nonneg _)
          rw [hz]
          positivity
      have hcomp := norm_iteratedFDeriv_comp_le hgCD huCD le_rfl x hCb hD
      refine hcomp.trans ?_
      have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [hfact]
      have : (6 : ℝ) * B * (2 / ε) ^ 3 = 48 * B / ε ^ 3 := by
        field_simp; ring
      rw [this]
    · -- off the shell `f` is locally constant, so the third derivative vanishes
      have hcont : Continuous fun y : EuclideanSpace ℝ (Fin k) => (‖y‖ ^ 2 - a ^ 2) / W := by
        fun_prop
      have hzero : iteratedFDeriv ℝ 3 (g ∘ u) x = 0 := by
        rcases not_and_or.mp hcase with hlt | hgt
        · have hvx : (‖x‖ ^ 2 - a ^ 2) / W < 0 := lt_of_not_ge hlt
          have hmem : {y : EuclideanSpace ℝ (Fin k) | (‖y‖ ^ 2 - a ^ 2) / W < 0} ∈ nhds x :=
            (isOpen_lt hcont continuous_const).mem_nhds hvx
          have heq : (g ∘ u) =ᶠ[nhds x] fun _ : EuclideanSpace ℝ (Fin k) => (1 : ℝ) :=
            Filter.eventually_of_mem hmem fun y hy => by
              rw [hval y]; exact radialCutoff_of_nonpos (le_of_lt hy)
          have := (Filter.EventuallyEq.iteratedFDeriv ℝ heq 3).self_of_nhds
          rw [this, iteratedFDeriv_const_of_ne (by norm_num)]
          rfl
        · have hvx : (1 : ℝ) < (‖x‖ ^ 2 - a ^ 2) / W := lt_of_not_ge hgt
          have hmem : {y : EuclideanSpace ℝ (Fin k) | 1 < (‖y‖ ^ 2 - a ^ 2) / W} ∈ nhds x :=
            (isOpen_lt continuous_const hcont).mem_nhds hvx
          have heq : (g ∘ u) =ᶠ[nhds x] fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ) :=
            Filter.eventually_of_mem hmem fun y hy => by
              rw [hval y]; exact radialCutoff_of_one_le (le_of_lt hy)
          have := (Filter.EventuallyEq.iteratedFDeriv ℝ heq 3).self_of_nhds
          rw [this, iteratedFDeriv_const_of_ne (by norm_num)]
          rfl
      rw [hzero, norm_zero]
      positivity

/-! #### Gaussian stability of the normalized sum

The right-hand endpoint of the Lindeberg telescope is the Gaussian law itself: replacing all
`n` summands by Gaussians and normalizing by `√n` reproduces `N(0, I_k)` exactly. This is
proved by characteristic functions — the `n`-fold product measure factorizes the integral
(`integral_fintype_prod_eq_prod`) and `charFun_stdGaussian` closes the computation. -/

/-- The characteristic function of the law of `c • ∑ᵢ yᵢ` under an `n`-fold product measure is
the `n`-th power of the characteristic function at `c • t`. -/
private lemma charFun_map_const_smul_sum {k n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] (c : ℝ)
    (t : EuclideanSpace ℝ (Fin k)) :
    charFun ((Measure.pi fun _ : Fin n => ν).map fun y => c • ∑ i, y i) t
      = charFun ν (c • t) ^ n := by
  classical
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hinner : ∀ y : Fin n → EuclideanSpace ℝ (Fin k),
      ⟪c • ∑ i, y i, t⟫_ℝ = ∑ i, ⟪y i, c • t⟫_ℝ := by
    intro y
    rw [real_inner_smul_left, sum_inner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (real_inner_smul_right _ _ _).symm
  have hfac : ∀ y : Fin n → EuclideanSpace ℝ (Fin k),
      Complex.exp ((⟪c • ∑ i, y i, t⟫_ℝ : ℂ) * Complex.I)
        = ∏ i, Complex.exp ((⟪y i, c • t⟫_ℝ : ℂ) * Complex.I) := by
    intro y
    rw [hinner y]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  simp_rw [hfac]
  refine Eq.trans (integral_fintype_prod_eq_prod (μ := fun _ : Fin n => ν)
    (fun (_ : Fin n) (x : EuclideanSpace ℝ (Fin k)) =>
      Complex.exp ((⟪x, c • t⟫_ℝ : ℂ) * Complex.I))) ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, charFun_apply]
  rfl

/-- **Gaussian stability of the normalized sum.** For `n ≥ 1`, pushing the `n`-fold product of
`N(0, I_k)` forward under `y ↦ n^{-1/2} ∑ᵢ yᵢ` gives back `N(0, I_k)`. -/
private lemma map_normalized_sum_stdGaussian {k n : ℕ} (hn : 0 < n) :
    ((Measure.pi fun _ : Fin n => stdGaussian (EuclideanSpace ℝ (Fin k))).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin n =>
      stdGaussian (EuclideanSpace ℝ (Fin k))).map
        fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_map_const_smul_sum, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_nat_mul]
  congr 1
  have hnorm : ‖(Real.sqrt (n : ℝ))⁻¹ • t‖ = ‖t‖ / Real.sqrt (n : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos)]
    ring
  have hsq : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnpos.le]
    norm_cast
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
  rw [hnorm]
  push_cast
  rw [div_pow, hsq]
  field_simp

/-! #### Ingredients of the one-step Lindeberg swap

Second-order Taylor expansion of `u ↦ f (v + c • u)` produces three integrals. The constant
term is trivial; the linear term vanishes because the law is centred (Riesz representative of
`Df(v)` plus `hmean`); and the quadratic term takes the **same value for any two laws with
identity covariance**, so no closed form for it is ever needed — only the fact that the two
values coincide. That last observation is what `integral_bilin_eq_basis_sum` records: it
evaluates `∫ D²f(v)(y,y)` as a fixed finite sum over the standard basis, whose value depends on
the law only through `hcov`. -/

section SwapStep

variable {k : ℕ}

/-- `L³ ⊆ L²` on a probability space, in the only form needed here: `t² ≤ 1 + t³`. -/
private lemma integrable_normSq_of_cube {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν := by
  have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin k) => 1 + ‖y‖ ^ 3) ν :=
    (integrable_const 1).add hβ
  refine Integrable.mono' hdom (by fun_prop) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  rcases le_or_gt ‖y‖ 1 with h | h
  · nlinarith
  · nlinarith

/-- `L¹ ⊆ L³` on a probability space, in the only form needed here: `t ≤ 1 + t³`. -/
private lemma integrable_norm_of_cube {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν := by
  have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin k) => 1 + ‖y‖ ^ 3) ν :=
    (integrable_const 1).add hβ
  refine Integrable.mono' hdom (by fun_prop) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
  rcases le_or_gt ‖y‖ 1 with h | h
  · nlinarith [pow_nonneg (norm_nonneg y) 3]
  · have ht2 : (1 : ℝ) ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    nlinarith [norm_nonneg y, ht2]

/-- A continuous linear functional is integrable as soon as the norm is: `|L y| ≤ ‖L‖ ‖y‖`. -/
private lemma integrable_clm_of_norm {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    Integrable (fun y => L y) ν := by
  refine Integrable.mono' (h1.const_mul ‖L‖) L.continuous.aestronglyMeasurable ?_
  filter_upwards with y
  exact L.le_opNorm y

/-- A continuous bilinear form evaluated on the diagonal is integrable as soon as the squared
norm is: `|B(y,y)| ≤ ‖B‖ ‖y‖²`. -/
private lemma integrable_bilin_of_normSq {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin k)) ℝ) :
    Integrable (fun y => B (fun _ => y)) ν := by
  refine Integrable.mono' (h2.const_mul ‖B‖)
    (B.cont.comp (continuous_pi fun _ => continuous_id)).aestronglyMeasurable ?_
  filter_upwards with y
  calc ‖B (fun _ => y)‖ ≤ ‖B‖ * ∏ _i : Fin 2, ‖y‖ := B.le_opNorm _
    _ = ‖B‖ * ‖y‖ ^ 2 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `y ↦ ⟪u, y⟫` is integrable as soon as the norm is. -/
private lemma integrable_inner_of_norm {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) ν)
    (u : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun y => ⟪u, y⟫_ℝ) ν :=
  integrable_clm_of_norm h1 (innerSL ℝ u)

/-- `y ↦ ⟪u, y⟫ ⟪v, y⟫` is integrable as soon as the squared norm is. -/
private lemma integrable_inner_mul_inner {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (u v : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun y => ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ) ν := by
  refine Integrable.mono' (h2.const_mul (‖u‖ * ‖v‖)) (by fun_prop) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul]
  calc |⟪u, y⟫_ℝ| * |⟪v, y⟫_ℝ| ≤ (‖u‖ * ‖y‖) * (‖v‖ * ‖y‖) :=
        mul_le_mul (abs_real_inner_le_norm u y) (abs_real_inner_le_norm v y)
          (abs_nonneg _) (by positivity)
    _ = ‖u‖ * ‖v‖ * ‖y‖ ^ 2 := by ring

/-- **The linear Taylor term integrates to zero against a centred law.** `Df(v)` is a continuous
linear functional, hence `⟪r, ·⟫` for its Riesz representative `r`, and `hmean` kills it. -/
private lemma integral_clm_eq_zero_of_centred {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    (∫ y, L y ∂ν) = 0 := by
  have hL : ∀ y : EuclideanSpace ℝ (Fin k),
      L y = ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm L, y⟫_ℝ :=
    fun y => (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
  simp_rw [hL]
  exact hmean _

/-- **The quadratic Taylor term depends on the law only through its covariance.** For a
continuous bilinear form `B` and *any* law with identity covariance, `∫ B(y,y)` equals the
explicit finite sum `∑_r ⟪e_{r₀}, e_{r₁}⟫ B(e_{r₀}, e_{r₁})` over `r : Fin 2 → Fin k`. Two such
laws therefore give the *same* value, which is exactly what the Lindeberg swap consumes; no
evaluation of the sum (`= ∑ₐ B(eₐ,eₐ)`) is needed. -/
private lemma integral_bilin_eq_basis_sum {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin k)) ℝ) :
    (∫ y, B (fun _ => y) ∂ν)
      = ∑ r : Fin 2 → Fin k,
          ⟪EuclideanSpace.basisFun (Fin k) ℝ (r 0),
            EuclideanSpace.basisFun (Fin k) ℝ (r 1)⟫_ℝ
            * B fun i => EuclideanSpace.basisFun (Fin k) ℝ (r i) := by
  classical
  set e : Fin k → EuclideanSpace ℝ (Fin k) := fun a => EuclideanSpace.basisFun (Fin k) ℝ a
    with he
  have hexp : ∀ y : EuclideanSpace ℝ (Fin k), B (fun _ => y)
      = ∑ r : Fin 2 → Fin k, ⟪e (r 0), y⟫_ℝ * ⟪e (r 1), y⟫_ℝ * B fun i => e (r i) := by
    intro y
    have hy : (fun _ : Fin 2 => y) = fun _ : Fin 2 => ∑ a, ⟪e a, y⟫_ℝ • e a := by
      funext _
      exact ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr' y).symm
    rw [hy, ← ContinuousMultilinearMap.coe_coe,
      (B.toMultilinearMap).map_sum (g := fun _ (a : Fin k) => ⟪e a, y⟫_ℝ • e a)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show (fun i : Fin 2 => ⟪e (r i), y⟫_ℝ • e (r i))
        = fun i : Fin 2 => (fun j : Fin 2 => ⟪e (r j), y⟫_ℝ) i • (fun j : Fin 2 => e (r j)) i
      from rfl, (B.toMultilinearMap).map_smul_univ, Fin.prod_univ_two,
      ContinuousMultilinearMap.coe_coe, smul_eq_mul]
  simp_rw [hexp]
  rw [integral_finset_sum _ fun r _ => (integrable_inner_mul_inner h2 _ _).mul_const _]
  exact Finset.sum_congr rfl fun r _ => by rw [integral_mul_const, hcov]

/-- **One step of the Lindeberg swap.** For a fixed shift `v` and scale `c ≥ 0`, replacing a
summand of law `ν` by one of law `ρ` — both centred and with identity covariance — costs at most
`(M/6) c³ (β_ν + β_ρ)`.

Both integrals are compared with the *same* number `f v + (c²/2) S`, where `S` is the
basis sum of `integral_bilin_eq_basis_sum`: the constant Taylor term is common, the linear term
vanishes on either side by `integral_clm_eq_zero_of_centred`, and the quadratic term has the
same value on either side because both laws have identity covariance. The two third-order
remainders are then bounded separately by `norm_taylor_remainder_three_le`. -/
private lemma abs_integral_swap_step_le {k : ℕ}
    {ν ρ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hmeanν : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcovν : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ν) = ⟪u, w⟫_ℝ)
    (hβν : Integrable (fun y => ‖y‖ ^ 3) ν)
    (hmeanρ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ρ) = 0)
    (hcovρ : ∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂ρ) = ⟪u, w⟫_ℝ)
    (hβρ : Integrable (fun y => ‖y‖ ^ 3) ρ)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f) (hfb : ∀ x, |f x| ≤ 1)
    {M : ℝ} (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M)
    (v : EuclideanSpace ℝ (Fin k)) {c : ℝ} (hc : 0 ≤ c) :
    |(∫ y, f (v + c • y) ∂ν) - (∫ y, f (v + c • y) ∂ρ)|
      ≤ M / 6 * c ^ 3 * ((∫ y, ‖y‖ ^ 3 ∂ν) + (∫ y, ‖y‖ ^ 3 ∂ρ)) := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := fderiv ℝ f v with hL
  set B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin k)) ℝ :=
    iteratedFDeriv ℝ 2 f v with hB
  set S : ℝ := ∑ r : Fin 2 → Fin k,
    ⟪EuclideanSpace.basisFun (Fin k) ℝ (r 0), EuclideanSpace.basisFun (Fin k) ℝ (r 1)⟫_ℝ
      * B fun i => EuclideanSpace.basisFun (Fin k) ℝ (r i) with hS
  -- The pointwise Taylor estimate against the *common* second-order polynomial.
  have htay : ∀ y : EuclideanSpace ℝ (Fin k),
      |f (v + c • y) - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)|
        ≤ M / 6 * c ^ 3 * ‖y‖ ^ 3 := by
    intro y
    have h := norm_taylor_remainder_three_le hf hM v (c • y)
    have h1 : fderiv ℝ f v (c • y) = c * L y := by rw [hL, map_smul, smul_eq_mul]
    have h2 : (B fun _ : Fin 2 => c • y) = c ^ 2 * B fun _ => y := by
      rw [show (fun _ : Fin 2 => c • y)
          = fun i : Fin 2 => (fun _ : Fin 2 => c) i • (fun _ : Fin 2 => y) i from rfl,
        ← ContinuousMultilinearMap.coe_coe, (B.toMultilinearMap).map_smul_univ,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ContinuousMultilinearMap.coe_coe, smul_eq_mul]
    have h3 : ‖c • y‖ ^ 3 = c ^ 3 * ‖y‖ ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
    rw [← hB, h1, h2, h3] at h
    calc |f (v + c • y) - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)|
        = |f (v + c • y) - f v - c * L y - 1 / 2 * (c ^ 2 * B fun _ => y)| := by ring_nf
      _ ≤ M / 6 * (c ^ 3 * ‖y‖ ^ 3) := h
      _ = M / 6 * c ^ 3 * ‖y‖ ^ 3 := by ring
  -- Each law is compared with the same number `f v + (c²/2) S`.
  have key : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂σ) = 0) →
      (∀ u w : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪w, y⟫_ℝ ∂σ) = ⟪u, w⟫_ℝ) →
      Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) σ →
      |(∫ y, f (v + c • y) ∂σ) - (f v + c ^ 2 / 2 * S)|
        ≤ M / 6 * c ^ 3 * ∫ y, ‖y‖ ^ 3 ∂σ := by
    intro σ hσ hm hcv hβ
    haveI := hσ
    have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) σ :=
      integrable_norm_of_cube hβ
    have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) σ :=
      integrable_normSq_of_cube hβ
    have ha : Integrable (fun y : EuclideanSpace ℝ (Fin k) => f v + c * L y) σ :=
      (integrable_const (f v)).add ((integrable_clm_of_norm h1 L).const_mul c)
    have hb : Integrable
        (fun y : EuclideanSpace ℝ (Fin k) => c ^ 2 / 2 * B fun _ => y) σ :=
      (integrable_bilin_of_normSq h2 B).const_mul (c ^ 2 / 2)
    have hPint : Integrable
        (fun y : EuclideanSpace ℝ (Fin k) => f v + c * L y + c ^ 2 / 2 * B fun _ => y) σ :=
      ha.add hb
    have hfint : Integrable (fun y : EuclideanSpace ℝ (Fin k) => f (v + c • y)) σ := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (hf.continuous.comp (by fun_prop)).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs]
      exact hfb _
    have hPval : (∫ y, (f v + c * L y + c ^ 2 / 2 * B fun _ => y) ∂σ)
        = f v + c ^ 2 / 2 * S := by
      rw [integral_add ha hb, integral_add (integrable_const (f v))
          ((integrable_clm_of_norm h1 L).const_mul c), integral_const, integral_const_mul,
        integral_const_mul, integral_clm_eq_zero_of_centred hm L,
        integral_bilin_eq_basis_sum hcv h2 B, ← hS]
      simp
    calc |(∫ y, f (v + c • y) ∂σ) - (f v + c ^ 2 / 2 * S)|
        = |∫ y, (f (v + c • y)
            - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)) ∂σ| := by
          rw [integral_sub hfint hPint, hPval]
      _ ≤ ∫ y, |f (v + c • y) - (f v + c * L y + c ^ 2 / 2 * B fun _ => y)| ∂σ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, M / 6 * c ^ 3 * ‖y‖ ^ 3 ∂σ :=
          integral_mono (hfint.sub hPint).abs (hβ.const_mul _) htay
      _ = M / 6 * c ^ 3 * ∫ y, ‖y‖ ^ 3 ∂σ := integral_const_mul _ _
  have hkν := key ν ‹_› hmeanν hcovν hβν
  have hkρ := key ρ ‹_› hmeanρ hcovρ hβρ
  have habs := abs_sub_abs_le_abs_sub ((∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S))
    ((∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S))
  have htri : |(∫ y, f (v + c • y) ∂ν) - (∫ y, f (v + c • y) ∂ρ)|
      ≤ |(∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S)|
        + |(∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S)| := by
    have := abs_sub ((∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S))
      ((∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S))
    calc |(∫ y, f (v + c • y) ∂ν) - (∫ y, f (v + c • y) ∂ρ)|
        = |((∫ y, f (v + c • y) ∂ν) - (f v + c ^ 2 / 2 * S))
            - ((∫ y, f (v + c • y) ∂ρ) - (f v + c ^ 2 / 2 * S))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  have hc3 : 0 ≤ M / 6 * c ^ 3 := by positivity
  nlinarith [hkν, hkρ, htri]

/-! #### Peeling one coordinate out of a product measure

The hybrid telescope replaces the summands one at a time, so each step must isolate a single
coordinate of a `Measure.pi` over a family of *unequal* laws. This is
`MeasureTheory.measurePreserving_piFinSuccAbove` (the coordinate `i` splits off as a `prod`
factor) followed by Fubini; the `Fin.insertNth` bookkeeping is `Fin.sum_univ_succAbove`. -/

/-- The (bounded, continuous) integrand of the peeled Fubini step is integrable on the
product. -/
private lemma integrable_peel_prod {k m : ℕ}
    (σ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure σ]
    (κ' : Fin m → Measure (EuclideanSpace ℝ (Fin k))) [∀ l, IsProbabilityMeasure (κ' l)]
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) (hgb : ∀ x, |g x| ≤ 1) :
    Integrable (fun p : EuclideanSpace ℝ (Fin k) × (Fin m → EuclideanSpace ℝ (Fin k)) =>
        g (p.1 + ∑ l, p.2 l)) (σ.prod (Measure.pi κ')) := by
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin k) × (Fin m → EuclideanSpace ℝ (Fin k)) =>
      p.1 + ∑ l, p.2 l) :=
    measurable_fst.add
      (Finset.univ.measurable_sum fun l _ => (measurable_pi_apply l).comp measurable_snd)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (hg.measurable.comp hmeas).aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  exact hgb _

/-- **Peeling one coordinate.** For a bounded continuous `g` and a finite family of probability
laws, the integral of `g (∑ₗ xₗ)` over `Measure.pi κ` is the iterated integral obtained by
singling out the coordinate `i`: the remaining coordinates supply the shift `∑ₗ yₗ` and the
`i`-th coordinate is integrated against `κ i`. -/
private lemma integral_pi_sum_peel {k m : ℕ}
    (κ : Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ i, IsProbabilityMeasure (κ i)] (i : Fin (m + 1))
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : Continuous g) (hgb : ∀ x, |g x| ≤ 1) :
    (∫ x, g (∑ l, x l) ∂(Measure.pi κ))
      = ∫ y, (∫ u, g (u + ∑ l, y l) ∂(κ i))
          ∂(Measure.pi fun l : Fin m => κ (i.succAbove l)) := by
  classical
  set e : ((_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k))
      ≃ᵐ EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => EuclideanSpace ℝ (Fin k)) i with he
  have hmp : MeasurePreserving e (Measure.pi κ)
      ((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) :=
    measurePreserving_piFinSuccAbove κ i
  have hsym : ∀ p : EuclideanSpace ℝ (Fin k) × ((_ : Fin m) → EuclideanSpace ℝ (Fin k)),
      (∑ l, (e.symm p) l) = p.1 + ∑ l, p.2 l := by
    intro p
    have hins : e.symm p = Fin.insertNth i p.1 p.2 := rfl
    rw [hins, Fin.sum_univ_succAbove _ i]
    simp
  have hF := integrable_peel_prod (κ i) (fun l : Fin m => κ (i.succAbove l)) hg hgb
  calc (∫ x, g (∑ l, x l) ∂(Measure.pi κ))
      = ∫ p, g (∑ l, (e.symm p) l)
          ∂((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) :=
        (MeasurePreserving.integral_comp' (MeasurePreserving.symm e hmp) _).symm
    _ = ∫ p, g (p.1 + ∑ l, p.2 l)
          ∂((κ i).prod (Measure.pi fun l : Fin m => κ (i.succAbove l))) := by
        simp_rw [hsym]
    _ = ∫ y, ∫ u, g (u + ∑ l, y l) ∂(κ i)
          ∂(Measure.pi fun l : Fin m => κ (i.succAbove l)) :=
        integral_prod_symm _ hF

end SwapStep

/-- **Lindeberg smooth-function comparison for the normalized sum.**
For a *fixed* `C³` test function `f` with `‖f‖_∞ ≤ 1` and `‖D³f‖ ≤ M`, replacing the `n` centred,
identity-covariance summands by Gaussians one at a time gives an error `≤ M (β + β_G) / (6√n)`,
where `β = ∫‖y‖³ dν` and `β_G = ∫‖z‖³ dN(0,I_k)`. This is `n^{-1/2}` for fixed `f`; the
degradation to `n^{-1/8}` for *sets* comes only from taking `f` a smoothed indicator with
`M ~ ε^{-3}` and optimising `ε`.

**Amendment (documented).** A boundedness hypothesis `hfb : ∀ x, |f x| ≤ 1` has been added.
The statement is true without it — `‖D³f‖ ≤ M` bounds `|f|` by a cubic polynomial, which is
`ν`-integrable by `hβ` and `Measure.pi`-integrable after a power-mean bound
`‖∑ yᵢ‖³ ≤ n² ∑ ‖yᵢ‖³` — but the resulting integrability bookkeeping is several hundred lines of
pure overhead. The lemma is `private`, and its only consumer,
`berryEsseen_ball_elementary`, applies it to smoothed indicators with values in `[0,1]`, which
supply `hfb` for free. No generality that any caller uses is lost.

The proof is the hybrid telescope over
`Qⱼ := Measure.pi (fun i => if i < j then γ else ν)`, `j = 0, …, n`, with

* `Q₀ = ⨂ⁿ ν`, whose pushforward under `n^{-1/2} ∑` is the left endpoint;
* `Qₙ = ⨂ⁿ γ`, whose pushforward is `γ` itself by `map_normalized_sum_stdGaussian`;
* each step `Qⱼ → Qⱼ₊₁` isolated by `integral_pi_sum_peel` (Fubini after
  `measurePreserving_piFinSuccAbove`) — the two hybrids differ *only* in the `j`-th factor, so
  after peeling that coordinate the outer measure over the remaining `n − 1` coordinates is
  literally the same, and the inner integrals differ by `abs_integral_swap_step_le` uniformly in
  the outer variable.

An earlier note preferred a doubled space `(⨂ν).prod (⨂γ)` with independence arguments, to
avoid "peeling a coordinate out of a product of unequal factors". That was the wrong call:
`measurePreserving_piFinSuccAbove` peels a coordinate out of a `Measure.pi` over an arbitrary
*dependent* family at no extra cost, and the hybrid family needs no independence API at all.

The `n` steps each cost `M/6 · n^{-3/2} (β + β_G)`, and `n · n^{-3/2} = n^{-1/2}`. -/
private lemma abs_integral_smooth_sub_gaussian_le {k n : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hn : 0 < n) (hν : IsProbabilityMeasure ν)
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f)
    -- USER-INPUT (amendment): the test function is bounded by `1`; see the docstring.
    (hfb : ∀ x, |f x| ≤ 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) :
    |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
      ≤ M / 6 * ((∫ y, ‖y‖ ^ 3 ∂ν)
          + (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)))
          / Real.sqrt (n : ℝ) := by
  classical
  haveI := hν
  -- The Gaussian side, transported to the Mathlib `stdGaussian` API.
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  haveI hγp : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  have hγstd : γ = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
    rw [hγdef]; exact multivariateGaussian_zero_one
  have hmeanγ : ∀ u : EuclideanSpace ℝ (Fin k), (∫ z, ⟪u, z⟫_ℝ ∂γ) = 0 := by
    intro u
    have h := integral_strongDual_stdGaussian (E := EuclideanSpace ℝ (Fin k)) (innerSL ℝ u)
    rw [hγstd]
    simpa using h
  have hcovγ : ∀ u w : EuclideanSpace ℝ (Fin k),
      (∫ z, ⟪u, z⟫_ℝ * ⟪w, z⟫_ℝ ∂γ) = ⟪u, w⟫_ℝ := by
    intro u w
    have hL2 : MemLp id 2 γ := by rw [hγstd]; exact IsGaussian.memLp_id _ 2 (by simp)
    have hid : γ[id] = (0 : EuclideanSpace ℝ (Fin k)) := by
      rw [hγstd]; exact integral_id_stdGaussian
    have h := covarianceBilin_apply (μ := γ) hL2 u w
    rw [hid] at h
    simp only [sub_zero] at h
    rw [← h, hγstd, covarianceBilin_stdGaussian]
    exact innerSL_apply_apply (𝕜 := ℝ) u w
  have hβγ : Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 3) γ := by
    have hL3 : MemLp id ((3 : ℕ) : ℝ≥0∞) γ := by
      rw [hγstd]; exact IsGaussian.memLp_id _ _ (by simp)
    simpa using hL3.integrable_norm_pow'
  -- Write `n = m + 1` so that a coordinate can be peeled off.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsN : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hNr
  set c : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hcdef
  have hc0 : 0 ≤ c := by positivity
  set g : EuclideanSpace ℝ (Fin k) → ℝ := fun z => f (c • z) with hgdef
  have hgcont : Continuous g := hf.continuous.comp (continuous_const_smul c)
  have hgb : ∀ x, |g x| ≤ 1 := fun x => hfb _
  -- The hybrid family and the telescoped functional.
  set κ : ℕ → Fin (m + 1) → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun j i => if (i : ℕ) < j then γ else ν with hκdef
  haveI hκp : ∀ (j : ℕ) (i : Fin (m + 1)), IsProbabilityMeasure (κ j i) := by
    intro j i
    rw [hκdef]
    dsimp only
    split_ifs
    · exact hγp
    · exact hν
  set I : ℕ → ℝ := fun j => ∫ x, g (∑ l, x l) ∂(Measure.pi (κ j)) with hIdef
  set X : ℝ := (∫ y, ‖y‖ ^ 3 ∂ν) + (∫ z, ‖z‖ ^ 3 ∂γ) with hXdef
  -- One telescope step.
  have hstep : ∀ j : ℕ, j < m + 1 → |I j - I (j + 1)| ≤ M / 6 * c ^ 3 * X := by
    intro j hj
    set i : Fin (m + 1) := ⟨j, hj⟩ with hidef
    have hival : (i : ℕ) = j := by rw [hidef]
    have hji : κ j i = ν := by
      rw [hκdef]; dsimp only; rw [if_neg (by rw [hival]; exact lt_irrefl j)]
    have hji1 : κ (j + 1) i = γ := by
      rw [hκdef]; dsimp only; rw [if_pos (by rw [hival]; exact Nat.lt_succ_self j)]
    have hoff : (fun l : Fin m => κ (j + 1) (i.succAbove l))
        = fun l : Fin m => κ j (i.succAbove l) := by
      funext l
      have hne : ((i.succAbove l : Fin (m + 1)) : ℕ) ≠ j := by
        intro h
        exact Fin.succAbove_ne i l (Fin.ext (by rw [h, hival]))
      rw [hκdef]
      dsimp only
      by_cases hlt : ((i.succAbove l : Fin (m + 1)) : ℕ) < j
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg hlt]
    have hpeel0 := integral_pi_sum_peel (κ j) i hgcont hgb
    have hpeel1 := integral_pi_sum_peel (κ (j + 1)) i hgcont hgb
    rw [hji] at hpeel0
    rw [hji1, hoff] at hpeel1
    set R : Measure ((_ : Fin m) → EuclideanSpace ℝ (Fin k)) :=
      Measure.pi (fun l : Fin m => κ j (i.succAbove l)) with hRdef
    haveI hRp : IsProbabilityMeasure R := by rw [hRdef]; infer_instance
    have hAint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
        ∫ u, g (u + ∑ l, y l) ∂ν) R :=
      (integrable_peel_prod ν (fun l : Fin m => κ j (i.succAbove l))
        hgcont hgb).integral_prod_right
    have hBint : Integrable (fun y : (_ : Fin m) → EuclideanSpace ℝ (Fin k) =>
        ∫ u, g (u + ∑ l, y l) ∂γ) R :=
      (integrable_peel_prod γ (fun l : Fin m => κ j (i.succAbove l))
        hgcont hgb).integral_prod_right
    have hpt : ∀ y : (_ : Fin m) → EuclideanSpace ℝ (Fin k),
        |(∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂γ)|
          ≤ M / 6 * c ^ 3 * X := by
      intro y
      have hrw : ∀ σ : Measure (EuclideanSpace ℝ (Fin k)),
          (∫ u, g (u + ∑ l, y l) ∂σ) = ∫ u, f ((c • ∑ l, y l) + c • u) ∂σ := by
        intro σ
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        rw [hgdef]
        dsimp only
        rw [smul_add, add_comm]
      rw [hrw ν, hrw γ, hXdef]
      exact abs_integral_swap_step_le hmean hcov hβ hmeanγ hcovγ hβγ hf hfb hM _ hc0
    have hIj : I j = ∫ y, (∫ u, g (u + ∑ l, y l) ∂ν) ∂R := by
      rw [hIdef]; exact hpeel0
    have hIj1 : I (j + 1) = ∫ y, (∫ u, g (u + ∑ l, y l) ∂γ) ∂R := by
      rw [hIdef]; exact hpeel1
    rw [hIj, hIj1, ← integral_sub hAint hBint]
    calc |∫ y, ((∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂γ)) ∂R|
        ≤ ∫ y, |(∫ u, g (u + ∑ l, y l) ∂ν) - (∫ u, g (u + ∑ l, y l) ∂γ)| ∂R :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _y, M / 6 * c ^ 3 * X ∂R :=
          integral_mono (hAint.sub hBint).abs (integrable_const _) hpt
      _ = M / 6 * c ^ 3 * X := by rw [integral_const]; simp
  -- Telescoping.
  have htel : ∀ j : ℕ, j ≤ m + 1 → |I 0 - I j| ≤ (j : ℝ) * (M / 6 * c ^ 3 * X) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j (by omega)
      have h3 : |I 0 - I (j + 1)| ≤ |I 0 - I j| + |I j - I (j + 1)| := abs_sub_le _ _ _
      push_cast
      linarith
  -- The two endpoints.
  have hκ0 : κ 0 = fun _ : Fin (m + 1) => ν := by
    funext i; rw [hκdef]; simp
  have hκN : κ (m + 1) = fun _ : Fin (m + 1) => γ := by
    funext i; rw [hκdef]; dsimp only; rw [if_pos i.isLt]
  have hI0 : I 0 = ∫ x, f x ∂((Measure.pi fun _ : Fin (m + 1) => ν).map
      fun y => c • ∑ i, y i) := by
    rw [integral_map (by fun_prop) hf.continuous.aestronglyMeasurable, hIdef]
    dsimp only
    rw [hκ0]
  have hIN : I (m + 1) = ∫ x, f x ∂γ := by
    have hmap : ((Measure.pi fun _ : Fin (m + 1) => γ).map fun y => c • ∑ i, y i) = γ := by
      rw [hγstd, hcdef]
      exact map_normalized_sum_stdGaussian (Nat.succ_pos m)
    rw [hIdef]
    dsimp only
    rw [hκN, ← integral_map (φ := fun y : (_ : Fin (m + 1)) → EuclideanSpace ℝ (Fin k) =>
      c • ∑ i, y i) (by fun_prop) hf.continuous.aestronglyMeasurable, hmap]
  have hfin := htel (m + 1) le_rfl
  rw [hI0, hIN] at hfin
  refine hfin.trans_eq ?_
  have hc2 : c ^ 2 = (((m + 1 : ℕ) : ℝ))⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt hNr.le]
  have hNc : ((m + 1 : ℕ) : ℝ) * c ^ 3 = c := by
    have hsplit : c ^ 3 = c ^ 2 * c := by ring
    rw [hsplit, hc2]
    field_simp
  calc (((m + 1 : ℕ) : ℝ)) * (M / 6 * c ^ 3 * X)
      = (((m + 1 : ℕ) : ℝ) * c ^ 3) * (M / 6 * X) := by ring
    _ = c * (M / 6 * X) := by rw [hNc]
    _ = M / 6 * X / Real.sqrt ((m + 1 : ℕ) : ℝ) := by rw [hcdef]; ring

/-! #### Moment facts consumed by the ball assembly

Two elementary consequences of the standing hypotheses (`hcov`, `hβ`, `ν` a probability
measure) that the `ε`-optimisation needs: the second moment is exactly the dimension, and
`β = ∫‖y‖³ dν` is bounded below by `k^{3/2}` (Lyapunov) — in particular `β > 0`, so that
`ε := (β/√n)^{1/4}` is a legitimate positive smoothing width. -/

/-- **The second moment is the dimension.** Under identity covariance,
`∫ ‖y‖² dν = k`. Expand `‖y‖² = ∑ᵢ ⟪eᵢ, y⟫²` over the standard orthonormal basis and apply
`hcov` coordinatewise; the interchange is legitimate because `hβ` makes each coordinate square
integrable. -/
private lemma integral_normSq_eq_dim {k : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    (∫ y, ‖y‖ ^ 2 ∂ν) = (k : ℝ) := by
  have hnormsq : ∀ y : EuclideanSpace ℝ (Fin k), ‖y‖ ^ 2 = ∑ i, y i ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  have hcoord : ∀ (i : Fin k) (y : EuclideanSpace ℝ (Fin k)),
      ⟪(EuclideanSpace.single i (1 : ℝ)), y⟫_ℝ = y i := by
    intro i y
    have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) y
    simpa using h
  have hsq2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
    integrable_normSq_of_cube hβ
  have hcomp : ∀ i : Fin k, Integrable (fun y : EuclideanSpace ℝ (Fin k) => y i ^ 2) ν := by
    intro i
    refine Integrable.mono' hsq2 (by fun_prop) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnormsq y]
    exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg (y j))
      (Finset.mem_univ i)
  calc (∫ y, ‖y‖ ^ 2 ∂ν) = ∫ y, ∑ i, y i ^ 2 ∂ν := by
        exact integral_congr_ae (ae_of_all _ fun y => hnormsq y)
    _ = ∑ i, ∫ y, y i ^ 2 ∂ν := integral_finset_sum _ fun i _ => hcomp i
    _ = ∑ _i : Fin k, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hone : ⟪(EuclideanSpace.single i (1 : ℝ)),
            (EuclideanSpace.single i (1 : ℝ))⟫_ℝ = 1 := by rw [hcoord]; simp
        have h := hcov (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
        rw [hone] at h
        simp only [hcoord] at h
        rw [← h]
        exact integral_congr_ae (ae_of_all _ fun y => by simp [sq])
    _ = (k : ℝ) := by simp

/-- **Lyapunov lower bound.** `k^{3/2} ≤ β` under identity covariance. Elementary: for every
`t ≥ 0` one has the pointwise inequality `3t‖y‖² ≤ 2‖y‖³ + t³` (it is
`(‖y‖ − t)²(2‖y‖ + t) ≥ 0`); integrating and taking `t = √k` gives `√k · k ≤ β`. -/
private lemma sqrt_dim_mul_dim_le_integral_norm_cube {k : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    Real.sqrt (k : ℝ) * (k : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂ν := by
  set t : ℝ := Real.sqrt (k : ℝ) with htdef
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hsq2 : Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) ν :=
    integrable_normSq_of_cube hβ
  have hmono : (∫ y, 3 * t * ‖y‖ ^ 2 ∂ν) ≤ ∫ y, (2 * ‖y‖ ^ 3 + t ^ 3) ∂ν := by
    refine integral_mono (hsq2.const_mul (3 * t)) ((hβ.const_mul 2).add (integrable_const _)) ?_
    intro y
    have hy : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    have hprod : (0 : ℝ) ≤ (‖y‖ - t) ^ 2 * (2 * ‖y‖ + t) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [hprod]
  rw [integral_const_mul, integral_add (hβ.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, integral_normSq_eq_dim hcov hβ] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  nlinarith [hmono, htsq, ht0]

/-! #### The Gaussian third moment `β_G = ∫‖z‖³ dN(0,I_k)`

The `ε`-optimisation also needs the *Gaussian* side of the third moment to be comparable to
`β`. Since `‖z‖² ∼ χ²_k`, the two public χ² moments (`integral_id_chiSquared` `E X = k`,
`variance_chiSquared` `E (X−k)² = 2k`) suffice, through the pointwise inequality

`r³ ≤ u r² + (r² − u²)²/(2u) + u (r² − u²)/2`, `u = √k`,

which is exactly `r²(u − r)² ≥ 0` after multiplying by `2u`. Integrating gives
`β_G ≤ k^{3/2} + √k ≤ 2 k^{3/2}`, and `k^{3/2} ≤ β` (Lyapunov) then gives `β_G ≤ 2β`. No
Cauchy–Schwarz and no fourth χ² moment are needed. -/

/-- Integrability of `x ↦ xⁿ` under `Gamma(a, r)`; the value of the moment is not needed, only
its finiteness. (`StatLean.MultipleTesting.GammaMoments` proves this but keeps it `private`.) -/
private lemma integrable_pow_gammaMeasure' {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (gammaMeasure a r) := by
  have hmeasG : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hmeasG
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hcongr : (fun x => x ^ n * (gammaPDF a r x).toReal)
      = fun x => x ^ n * gammaPDFReal a r x := by
    funext x
    rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rw [hcongr]
  have hmodel : IntegrableOn (fun x => x ^ (a + (n : ℝ) - 1) * Real.exp (-(r * x)))
      (Set.Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + (n : ℝ) - 1) (b := r)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) le_rfl hr
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [Real.rpow_one, neg_mul]
  have hIoi : IntegrableOn (fun x => x ^ n * gammaPDFReal a r x) (Set.Ioi (0 : ℝ)) volume := by
    refine IntegrableOn.congr_fun (hmodel.const_mul (r ^ a / Real.Gamma a))
      (fun x hx => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hx
    rw [gammaPDFReal, if_pos hx.le, ← Real.rpow_natCast x n,
      show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add hx (a - 1) (n : ℝ)]
    ring
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, hIoi⟩
  refine integrableOn_zero.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [Set.mem_setOf_eq, Classical.not_imp, Set.mem_Iic] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (show x ^ n * gammaPDFReal a r x = 0 by
      rw [gammaPDFReal, if_neg (not_le.mpr h), mul_zero]).symm hx2
  · exact h

/-- Integrability of `x ↦ xⁿ` under `χ²_k`. -/
private lemma integrable_pow_chiSquared {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Integrable (fun x => x ^ n) (StatLean.MultipleTesting.chiSquared k) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold StatLean.MultipleTesting.chiSquared
  exact integrable_pow_gammaMeasure' (by linarith) (by norm_num) n

/-- The squared norm pushes `N(0, I_k)` forward to `χ²_k` (`0 < k`). -/
private lemma gaussian_map_normSq {k : ℕ} (hk : 0 < k) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map (fun z => ‖z‖ ^ 2)
      = StatLean.MultipleTesting.chiSquared k := by
  rw [map_normSq_multivariateGaussian_of_norm_eq k 0 (by simp), noncentralChiSquared_zero hk]

/-- **The standard Gaussian has no atom at the origin** (`0 < k`): the ball `{‖z‖ ≤ 0}` is the
preimage of `{0}` under `‖·‖²`, whose law `χ²_k` has a Lebesgue density. -/
private lemma gaussian_origin_measure_zero {k : ℕ} (hk : 0 < k) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) {z | ‖z‖ ≤ 0} = 0 := by
  have hset : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ 0} = (fun z => ‖z‖ ^ 2) ⁻¹' {0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hz : ‖z‖ = 0 := le_antisymm h (norm_nonneg z)
      rw [hz]; ring
    · intro h
      have hz : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
      exact le_of_eq hz
  rw [hset, ← Measure.map_apply (by fun_prop) (measurableSet_singleton 0), gaussian_map_normSq hk]
  unfold StatLean.MultipleTesting.chiSquared ProbabilityTheory.gammaMeasure
  rw [withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ (by simp)]

/-- **The Gaussian third moment is at most `2 k^{3/2}`.** Combined with the Lyapunov bound
`k^{3/2} ≤ β` this gives `β_G ≤ 2 β`, the comparison the ball assembly consumes. -/
private lemma integral_norm_cube_gaussian_le {k : ℕ} (hk : 0 < k) :
    ∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      ≤ 2 * (Real.sqrt (k : ℝ) * (k : ℝ)) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  set E := EuclideanSpace ℝ (Fin k)
  set γ : Measure E := multivariateGaussian (0 : E) 1 with hγ
  set u : ℝ := Real.sqrt (k : ℝ) with hu_def
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : 0 < u := Real.sqrt_pos.mpr hkr
  have hk2 : (k : ℝ) = u ^ 2 := (Real.sq_sqrt hkr.le).symm
  have hmap := gaussian_map_normSq hk
  have hae : AEMeasurable (fun z : E => ‖z‖ ^ 2) γ := (by fun_prop : Measurable _).aemeasurable
  -- the two χ² moments, transported back to `γ`
  have h2 : ∫ z, ‖z‖ ^ 2 ∂γ = (k : ℝ) := by
    have hchi := StatLean.MultipleTesting.integral_id_chiSquared hk
    rw [← hmap, integral_map hae (by fun_prop)] at hchi
    exact hchi
  have h4 : ∫ z, (‖z‖ ^ 2 - (k : ℝ)) ^ 2 ∂γ = 2 * (k : ℝ) := by
    have hchi := StatLean.MultipleTesting.variance_chiSquared hk
    rw [← hmap, integral_map hae (by fun_prop)] at hchi
    exact hchi
  -- integrability of the two transported moments
  have hI2 : Integrable (fun z : E => ‖z‖ ^ 2) γ := by
    have h := integrable_pow_chiSquared hk 1
    rw [← hmap] at h
    have := (integrable_map_measure (by fun_prop) hae).mp h
    simpa [Function.comp_def] using this
  have hI4 : Integrable (fun z : E => (‖z‖ ^ 2 - (k : ℝ)) ^ 2) γ := by
    have hpoly : Integrable (fun x : ℝ => (x - (k : ℝ)) ^ 2)
        (StatLean.MultipleTesting.chiSquared k) := by
      have ha := integrable_pow_chiSquared hk 2
      have hb : Integrable (fun x : ℝ => x) (StatLean.MultipleTesting.chiSquared k) := by
        simpa using integrable_pow_chiSquared hk 1
      have hc : Integrable (fun _ : ℝ => (k : ℝ) ^ 2)
          (StatLean.MultipleTesting.chiSquared k) := integrable_const _
      have h0 := (ha.sub (hb.const_mul (2 * (k : ℝ)))).add hc
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [← hmap] at hpoly
    have := (integrable_map_measure (by fun_prop) hae).mp hpoly
    simpa [Function.comp_def] using this
  -- the three summands of the majorant, each with a clean applied-lambda type
  have e1 : Integrable (fun z : E => u * ‖z‖ ^ 2) γ := hI2.const_mul u
  have e2 : Integrable (fun z : E => (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)) γ :=
    hI4.div_const (2 * u)
  have e3 : Integrable (fun z : E => u * (‖z‖ ^ 2 - (k : ℝ)) / 2) γ := by
    have h0 := ((hI2.const_mul u).sub (integrable_const (u * (k : ℝ)))).div_const 2
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have e12 : Integrable (fun z : E => u * ‖z‖ ^ 2
      + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)) γ := by
    have h0 := e1.add e2
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
  have hFint : Integrable (fun z : E => u * ‖z‖ ^ 2
      + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u) + u * (‖z‖ ^ 2 - (k : ℝ)) / 2) γ := by
    have h0 := e12.add e3
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
  -- the pointwise inequality `r³ ≤ u r² + (r² − u²)²/(2u) + u (r² − u²)/2`
  have hpt : ∀ z : E, ‖z‖ ^ 3 ≤ u * ‖z‖ ^ 2
      + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u) + u * (‖z‖ ^ 2 - (k : ℝ)) / 2 := by
    intro z
    rw [← sub_nonneg]
    have hid : u * ‖z‖ ^ 2 + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)
        + u * (‖z‖ ^ 2 - (k : ℝ)) / 2 - ‖z‖ ^ 3
        = ‖z‖ ^ 2 * (u - ‖z‖) ^ 2 / (2 * u) := by
      rw [hk2]; field_simp; ring
    rw [hid]
    positivity
  have hcube : Integrable (fun z : E => ‖z‖ ^ 3) γ := by
    refine Integrable.mono' hFint (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt z
  have hFval : ∫ z, (u * ‖z‖ ^ 2 + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)
      + u * (‖z‖ ^ 2 - (k : ℝ)) / 2) ∂γ = u * (k : ℝ) + (k : ℝ) / u := by
    have hsub : Integrable (fun z : E => ‖z‖ ^ 2 - (k : ℝ)) γ := by
      have h0 := hI2.sub (integrable_const (k : ℝ))
      refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply]
    rw [integral_add e12 e3, integral_add e1 e2, integral_const_mul, integral_div,
      integral_div, integral_const_mul, integral_sub hI2 (integrable_const (k : ℝ)),
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [h2, h4]
    field_simp
    ring
  calc ∫ z, ‖z‖ ^ 3 ∂γ
      ≤ ∫ z, (u * ‖z‖ ^ 2 + (‖z‖ ^ 2 - (k : ℝ)) ^ 2 / (2 * u)
          + u * (‖z‖ ^ 2 - (k : ℝ)) / 2) ∂γ := integral_mono hcube hFint hpt
    _ = u * (k : ℝ) + (k : ℝ) / u := hFval
    _ ≤ 2 * (u * (k : ℝ)) := by
        have hku : (k : ℝ) / u = u := by
          rw [hk2]; field_simp
        rw [hku]
        have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith [hu, h1]

/-- **`β > 0`.** If `β = ∫‖y‖³ dν` vanished then `ν` would be the Dirac mass at the origin, whose
second moment is `0` and not `k > 0`. -/
private lemma integral_norm_cube_pos {k : ℕ} (hk : 0 < k)
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure ν]
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν) :
    0 < ∫ y, ‖y‖ ^ 3 ∂ν := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have h := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβ
  nlinarith [h, hsk, hk0]

/-- **Elementary ball Berry–Esseen bound, with a dimension-free constant (honest, non-sharp).**
There is an *absolute* constant `C` — independent of the dimension `k`, the sample size `n` and
the sampling law `ν` — such that the normal approximation to the law of `‖n^{-1/2} ∑ᵢ Yᵢ‖²` over
half-lines `{‖z‖² ≤ t}` is accurate to `C · (β/√n)^{1/4}`, where `β = ∫‖y‖³ dν`. This is the
*honest* output of the elementary "smooth the indicator + Lindeberg swap" route for **balls**:
the constant is dimension-free (the ball anti-concentration `gaussian_ball_shell_measure_le` and
the radial smoothing `exists_smoothed_radial_indicator` both have dimension-free constants), but
the rate is `(β/√n)^{1/4} = n^{-1/8}`, **not** Bentkus's `β/√n = n^{-1/2}`. The degradation is
intrinsic to the mollifier method (see the module docstring).

Assembly (the `ε`-optimisation): for the set `{‖z‖ ≤ s}` (`s = √t`) sandwich the indicator between
two smoothed radial indicators of widths `ε` (`exists_smoothed_radial_indicator`); the swap
`abs_integral_smooth_sub_gaussian_le` bounds `|E f(Sₙ) − E f(G)| ≤ (C₃/ε³)(β + β_G)/(6√n)`, and the
Gaussian shell mass of `{s < ‖z‖ ≤ s+ε}` is `≤ C_ac ε` (`gaussian_ball_shell_measure_le`). Adding
and choosing `ε = (β/√n)^{1/4}` balances `ε⁻³ · β/√n` against `ε` at `(β/√n)^{1/4}`.

**State of the assembly.** Two of the three geometric bricks are now *proved unconditionally*
and with dimension-free constants:

* `gaussian_ball_shell_measure_le` (`C_ac = 7`) — no longer conditional on any `Γ`-Stirling
  estimate, see `chiSquared_density_mul_sqrt_le`;
* `exists_smoothed_radial_indicator` (`C₃ = 48 B`) — proved through the squared-norm route, so
  it holds for **every** `0 ≤ a` and `ε > 0`. In particular the small-radius case `√t < ε`,
  which the older `χ ∘ ‖·‖` formulation had to treat separately (its `ε ≤ a` hypothesis is
  gone), no longer needs any special handling.

The moment facts the `ε`-optimisation needs are also proved here:
`integral_normSq_eq_dim` (`∫‖y‖² dν = k`), `sqrt_dim_mul_dim_le_integral_norm_cube` (Lyapunov,
`k^{3/2} ≤ β`) and `integral_norm_cube_pos` (`β > 0`, so `ε := (β/√n)^{1/4}` is a legitimate
positive width).

The Gaussian side of the third moment is now proved too: `integral_norm_cube_gaussian_le`
gives `β_G ≤ 2 k^{3/2} ≤ 2 β` from the two *public* χ² moments (`E X = k`, `E (X−k)² = 2k`)
— no fourth χ² moment and no Cauchy–Schwarz are needed, see its docstring.

**The assembly below is complete and consumes nothing on faith**: its last ingredient,
`abs_integral_smooth_sub_gaussian_le` (the third-order multivariate Lindeberg swap), is proved
above, so `berryEsseen_ball_elementary` is axiom-clean. Concretely, with `ε := (β/√n)^{1/4}`:

* upper: `μₙ{‖z‖ ≤ s} ≤ ∫ f_ε dμₙ ≤ ∫ f_ε dγ + (C₃/ε³)(β+β_G)/(6√n) ≤ γ{‖z‖ ≤ s+ε} + (C₃/2)ε`
  with `f_ε` the smoothed radial indicator at radius `s`, and then
  `γ{‖z‖ ≤ s+ε} ≤ γ{‖z‖ ≤ s} + C_ac ε` by shell anti-concentration;
* lower: the same with the smoothed indicator at radius `s − ε` when `ε ≤ s`; when `s < ε` the
  ball is contained in `{‖z‖ ≤ ε}` and the shell bound at radius `0` closes it directly (the
  Gaussian has no atom at the origin, `gaussian_origin_measure_zero`).

Both `(β/√n)/ε³ = ε` steps are the `ε`-balance, and the resulting absolute constant is
`C = C_ac + C₃/2`. -/
theorem berryEsseen_ball_elementary :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ),
      0 < n → 0 < k → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
              {z | ‖z‖ ^ 2 ≤ t}).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := exists_smoothed_radial_indicator
  obtain ⟨Cac, hCacpos, hCac⟩ := gaussian_ball_shell_measure_le
  refine ⟨Cac + C₃ / 2, by positivity, ?_⟩
  intro k n ν t hn hk hνp hmean hcov hβint
  haveI := hνp
  -- abbreviations for the two laws being compared
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  -- the smoothing width `ε = (β/√n)^{1/4}`
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  set ε : ℝ := q ^ ((1 : ℝ) / 4) with hεdef
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hqpos _
  have hεq : ε ^ 3 * ε = q := by
    rw [hεdef, ← Real.rpow_natCast (q ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hqpos.le,
      ← Real.rpow_add hqpos]
    norm_num
  have hq3 : q / ε ^ 3 = ε := by
    rw [← hεq]; field_simp
  -- the Gaussian third moment is at most `2β`
  have hβGle : (∫ z, ‖z‖ ^ 3 ∂γ) ≤ 2 * β := by
    have h1 := integral_norm_cube_gaussian_le (k := k) hk
    rw [← hγdef] at h1
    have h2 := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h2
    linarith
  -- the Lindeberg swap, with the `ε`-balance already carried out
  have herr : ∀ f : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 3 f → (∀ x, |f x| ≤ 1) →
      (∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ C₃ / ε ^ 3) →
      |(∫ x, f x ∂μ) - (∫ x, f x ∂γ)| ≤ C₃ / 2 * ε := by
    intro f hfcd hfbd hfD3
    have hswap := abs_integral_smooth_sub_gaussian_le (ν := ν) hn hνp hmean hcov hβint hfcd hfbd
      (M := C₃ / ε ^ 3) (by positivity) hfD3
    rw [← hμdef, ← hγdef, ← hβdef] at hswap
    refine hswap.trans ?_
    have hA : 0 ≤ C₃ / ε ^ 3 / 6 := by positivity
    have h3q : (β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ) ≤ 3 * q := by
      rw [hqdef, div_le_iff₀ hsn]
      have hcancel : 3 * (β / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 3 * β := by
        field_simp
      rw [hcancel]
      linarith
    calc C₃ / ε ^ 3 / 6 * (β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ)
        = C₃ / ε ^ 3 / 6 * ((β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ C₃ / ε ^ 3 / 6 * (3 * q) := mul_le_mul_of_nonneg_left h3q hA
      _ = C₃ / 2 * (q / ε ^ 3) := by ring
      _ = C₃ / 2 * ε := by rw [hq3]
  -- measurability of the balls, and the two sandwich steps
  have hballmeas : ∀ a : ℝ, MeasurableSet {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} :=
    fun a => measurableSet_le (by fun_prop) measurable_const
  have hlow : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))), IsProbabilityMeasure ρ →
      ∀ (f : EuclideanSpace ℝ (Fin k) → ℝ) (a : ℝ), Integrable f ρ → (∀ x, 0 ≤ f x) →
      (∀ x, ‖x‖ ≤ a → f x = 1) → (ρ {z | ‖z‖ ≤ a}).toReal ≤ ∫ x, f x ∂ρ := by
    intro ρ hρ f a hfint hf0 hone
    haveI := hρ
    have hind : Integrable (Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a}
        (fun _ => (1 : ℝ))) ρ := by
      rw [integrable_indicator_iff (hballmeas a)]
      exact integrableOn_const (measure_ne_top _ _)
    calc (ρ {z | ‖z‖ ≤ a}).toReal
        = ∫ x, Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} (fun _ => (1 : ℝ)) x ∂ρ := by
          rw [integral_indicator (hballmeas a), setIntegral_const, measureReal_def, smul_eq_mul,
            mul_one]
      _ ≤ ∫ x, f x ∂ρ := by
          refine integral_mono hind hfint fun x => ?_
          by_cases hx : ‖x‖ ≤ a
          · rw [Set.indicator_of_mem (show x ∈ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} from hx),
              hone x hx]
          · rw [Set.indicator_of_notMem (show x ∉ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ a} from hx)]
            exact hf0 x
  have hupp : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))), IsProbabilityMeasure ρ →
      ∀ (f : EuclideanSpace ℝ (Fin k) → ℝ) (b : ℝ), Integrable f ρ → (∀ x, f x ≤ 1) →
      (∀ x, b < ‖x‖ → f x = 0) → (∫ x, f x ∂ρ) ≤ (ρ {z | ‖z‖ ≤ b}).toReal := by
    intro ρ hρ f b hfint hf1 hzero
    haveI := hρ
    have hind : Integrable (Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b}
        (fun _ => (1 : ℝ))) ρ := by
      rw [integrable_indicator_iff (hballmeas b)]
      exact integrableOn_const (measure_ne_top _ _)
    calc (∫ x, f x ∂ρ)
        ≤ ∫ x, Set.indicator {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b} (fun _ => (1 : ℝ)) x ∂ρ := by
          refine integral_mono hfint hind fun x => ?_
          by_cases hx : ‖x‖ ≤ b
          · rw [Set.indicator_of_mem (show x ∈ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b} from hx)]
            exact hf1 x
          · rw [Set.indicator_of_notMem (show x ∉ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b} from hx),
              hzero x (not_le.mp hx)]
      _ = (ρ {z | ‖z‖ ≤ b}).toReal := by
          rw [integral_indicator (hballmeas b), setIntegral_const, measureReal_def, smul_eq_mul,
            mul_one]
  -- shell anti-concentration in the two-ball form
  have hshell : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (γ {z | ‖z‖ ≤ b}).toReal ≤ (γ {z | ‖z‖ ≤ a}).toReal + Cac * (b - a) := by
    intro a b ha hab
    have h1 := hCac k hk a (b - a) ha (by linarith)
    rw [show a + (b - a) = b from by ring, ← hγdef] at h1
    have hsub : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ b}
        ⊆ {z | ‖z‖ ≤ a} ∪ {z | a < ‖z‖ ∧ ‖z‖ ≤ b} := by
      intro z hz
      rcases le_or_gt ‖z‖ a with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hz⟩
    have h2 : γ {z | ‖z‖ ≤ b} ≤ γ {z | ‖z‖ ≤ a} + γ {z | a < ‖z‖ ∧ ‖z‖ ≤ b} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have h3 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h3
    linarith
  -- integrability of any `[0,1]`-valued continuous test function
  have hfint : ∀ (ρ : Measure (EuclideanSpace ℝ (Fin k))), IsProbabilityMeasure ρ →
      ∀ f : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 3 f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      Integrable f ρ := by
    intro ρ hρ f hfcd hf0 hf1
    haveI := hρ
    refine Integrable.mono' (integrable_const (1 : ℝ)) hfcd.continuous.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hf1 x
  rcases lt_or_ge t 0 with ht | ht
  · -- degenerate case: the ball is empty
    have hempty : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ t} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht (sq_nonneg _)
    rw [hempty]
    simp only [measure_empty, ENNReal.toReal_zero, sub_zero, abs_zero]
    have : 0 < (Cac + C₃ / 2) * ε := mul_pos (by linarith) hεpos
    linarith
  · -- the ball is `{‖z‖ ≤ s}` with `s = √t`
    set s : ℝ := Real.sqrt t with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg t
    have hSset : {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ t} = {z | ‖z‖ ≤ s} := by
      ext z
      simp only [Set.mem_setOf_eq, hsdef]
      constructor
      · intro h
        rw [← Real.sqrt_sq (norm_nonneg z)]
        exact Real.sqrt_le_sqrt h
      · intro h
        have hmul := mul_self_le_mul_self (norm_nonneg z) h
        rw [Real.mul_self_sqrt ht] at hmul
        rw [pow_two]; exact hmul
    rw [hSset]
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · -- upper deviation
      obtain ⟨f, hfcd, hf0, hf1, hfone, hfzero, hfD3⟩ := hC₃ k s hs0 hεpos
      have hIμ := hfint μ hμprob f hfcd hf0 hf1
      have hIγ := hfint γ hγprob f hfcd hf0 hf1
      have hswap := herr f hfcd (fun x => abs_le.mpr ⟨by linarith [hf0 x], hf1 x⟩) hfD3
      rw [abs_sub_le_iff] at hswap
      have hchain : (μ {z | ‖z‖ ≤ s}).toReal
          ≤ (γ {z | ‖z‖ ≤ s}).toReal + (Cac + C₃ / 2) * ε := by
        calc (μ {z | ‖z‖ ≤ s}).toReal
            ≤ ∫ x, f x ∂μ := hlow μ hμprob f s hIμ hf0 hfone
          _ ≤ (∫ x, f x ∂γ) + C₃ / 2 * ε := by linarith [hswap.1]
          _ ≤ (γ {z | ‖z‖ ≤ s + ε}).toReal + C₃ / 2 * ε := by
              have := hupp γ hγprob f (s + ε) hIγ hf1 hfzero
              linarith
          _ ≤ ((γ {z | ‖z‖ ≤ s}).toReal + Cac * (s + ε - s)) + C₃ / 2 * ε := by
              have := hshell s (s + ε) hs0 (by linarith)
              linarith
          _ = (γ {z | ‖z‖ ≤ s}).toReal + (Cac + C₃ / 2) * ε := by ring
      linarith
    · -- lower deviation
      rcases le_or_gt ε s with hse | hse
      · obtain ⟨f, hfcd, hf0, hf1, hfone, hfzero, hfD3⟩ := hC₃ k (s - ε) (by linarith) hεpos
        have hfzero' : ∀ x, s < ‖x‖ → f x = 0 := fun x hx => hfzero x (by linarith)
        have hIμ := hfint μ hμprob f hfcd hf0 hf1
        have hIγ := hfint γ hγprob f hfcd hf0 hf1
        have hswap := herr f hfcd (fun x => abs_le.mpr ⟨by linarith [hf0 x], hf1 x⟩) hfD3
        rw [abs_sub_le_iff] at hswap
        have hchain : (γ {z | ‖z‖ ≤ s}).toReal
            ≤ (μ {z | ‖z‖ ≤ s}).toReal + (Cac + C₃ / 2) * ε := by
          calc (γ {z | ‖z‖ ≤ s}).toReal
              ≤ (γ {z | ‖z‖ ≤ s - ε}).toReal + Cac * (s - (s - ε)) :=
                hshell (s - ε) s (by linarith) (by linarith)
            _ ≤ (∫ x, f x ∂γ) + Cac * ε := by
                have := hlow γ hγprob f (s - ε) hIγ hf0 hfone
                have harith : s - (s - ε) = ε := by ring
                rw [harith]
                linarith
            _ ≤ ((∫ x, f x ∂μ) + C₃ / 2 * ε) + Cac * ε := by linarith [hswap.2]
            _ ≤ ((μ {z | ‖z‖ ≤ s}).toReal + C₃ / 2 * ε) + Cac * ε := by
                have := hupp μ hμprob f s hIμ hf1 hfzero'
                linarith
            _ = (μ {z | ‖z‖ ≤ s}).toReal + (Cac + C₃ / 2) * ε := by ring
        linarith
      · -- `s < ε`: the ball is inside `{‖z‖ ≤ ε}` and the Gaussian has no atom at the origin
        have h1 := hshell 0 s le_rfl hs0
        have h0 : γ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ 0} = 0 := by
          rw [hγdef]; exact gaussian_origin_measure_zero hk
        rw [h0] at h1
        simp only [ENNReal.toReal_zero, zero_add] at h1
        have h2 : (0 : ℝ) ≤ (μ {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ≤ s}).toReal :=
          ENNReal.toReal_nonneg
        have h3 : Cac * (s - 0) ≤ Cac * ε :=
          mul_le_mul_of_nonneg_left (by linarith) hCacpos.le
        have h4 : 0 ≤ C₃ / 2 * ε := by positivity
        linarith

/-! #### The convex headline in Lévy (thickening) form

The convex headline `berryEsseen_convex_elementary` is assembled in two steps. The first — and
the one where the mollification of `exists_smoothed_convex_indicator` is actually consumed — is
the Lévy/Prokhorov-type inequality between `μₙ(B)` and `γ(Bᵋ)` (rather than between `μₙ(B)` and
`γ(B)`), which needs no boundary-shell input at all. That is `berryEsseen_convex_levy_elementary`
below. The second step collapses `γ(Bᵋ)` back to `γ(B)` (and dually `γ(B)` to `γ(B₋ᵋ)`) at cost
`C_k ε`; that is `gaussian_thickening_le` / `gaussian_le_erosion_add` of
`StatLean.HypothesisTesting.ForMathlib.GaussianShell`. Nothing else is needed, and the headline
follows by the same `ε`-balance as `berryEsseen_ball_elementary`. -/

/-- Lower sandwich: a nonnegative test function equal to `1` on a measurable set dominates that
set's indicator. -/
private lemma measureReal_le_integral_of_eq_one {k : ℕ}
    {ρ : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ρ]
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {S : Set (EuclideanSpace ℝ (Fin k))}
    (hS : MeasurableSet S) (hfint : Integrable f ρ) (hf0 : ∀ x, 0 ≤ f x)
    (hone : ∀ x ∈ S, f x = 1) : (ρ S).toReal ≤ ∫ x, f x ∂ρ := by
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (measure_ne_top _ _)
  calc (ρ S).toReal = ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂ρ := by
        rw [integral_indicator hS, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    _ ≤ ∫ x, f x ∂ρ := by
        refine integral_mono hind hfint fun x => ?_
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hone x hx]
        · rw [Set.indicator_of_notMem hx]; exact hf0 x

/-- Upper sandwich: a test function bounded by `1` and supported in a measurable set is dominated
by that set's indicator. -/
private lemma integral_le_measureReal_of_support_subset {k : ℕ}
    {ρ : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ρ]
    {f : EuclideanSpace ℝ (Fin k) → ℝ} {S : Set (EuclideanSpace ℝ (Fin k))}
    (hS : MeasurableSet S) (hfint : Integrable f ρ) (hf1 : ∀ x, f x ≤ 1)
    (hsupp : ∀ x, f x ≠ 0 → x ∈ S) : (∫ x, f x ∂ρ) ≤ (ρ S).toReal := by
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (measure_ne_top _ _)
  calc (∫ x, f x ∂ρ) ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂ρ := by
        refine integral_mono hfint hind fun x => ?_
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx]; exact hf1 x
        · rw [Set.indicator_of_notMem hx]
          by_contra hcon
          exact hx (hsupp x (ne_of_gt (not_le.1 hcon)))
    _ = (ρ S).toReal := by
        rw [integral_indicator hS, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

/-- **Elementary convex Berry–Esseen bound, Lévy (thickening) form.** For every dimension `k > 0`
there is a constant `C` such that for every convex measurable `B`, every width `ε > 0` and every
`n > 0`,

`μₙ(B) ≤ γ(Bᵋ) + C (β/√n)/ε³` and `γ(B) ≤ μₙ(Bᵋ) + C (β/√n)/ε³`,

where `μₙ` is the law of the normalized sum, `γ = N(0, I_k)`, `β = ∫‖y‖³ dν` and `Bᵋ` is the
`ε`-thickening of `B`.

Both inequalities are the Lindeberg swap `abs_integral_smooth_sub_gaussian_le` applied to the
smoothed indicator of `exists_smoothed_convex_indicator`, sandwiched between `1_B` and `1_{Bᵋ}`;
`C = C₃/2` where `C₃` is the third-derivative constant of the smoothed indicator (the factor
`3 ≥ (β + β_G)/β` from `integral_norm_cube_gaussian_le` is what turns `C₃/6` into `C₃/2`).

This is the whole analytic content of `berryEsseen_convex_elementary`: taking `ε = (β/√n)^{1/4}`
here gives `μₙ(B) ≤ γ(Bᵋ) + C ε` and `γ(B) ≤ μₙ(Bᵋ) + C ε`, and the only remaining step is to
replace `γ(Bᵋ)` by `γ(B) + C_k ε` (and, applying the second inequality to the erosion of `B`,
`γ(B)` by `γ(B₋ᵋ) + C_k ε`), which is `gaussian_thickening_le` / `gaussian_le_erosion_add` of
`StatLean.HypothesisTesting.ForMathlib.GaussianShell`. -/
theorem berryEsseen_convex_levy_elementary {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))) (ε : ℝ),
      0 < n → 0 < ε → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      ((((Measure.pi fun _ : Fin n => ν).map
              fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
            ≤ ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
                (Metric.thickening ε B)).toReal
              + C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε ^ 3)
        ∧ (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal
            ≤ (((Measure.pi fun _ : Fin n => ν).map
                fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
                  (Metric.thickening ε B)).toReal
              + C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) / ε ^ 3) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := exists_smoothed_convex_indicator k
  refine ⟨C₃ / 2, by positivity, ?_⟩
  intro n ν B ε hn hε hνp hmean hcov hβint hBmeas hBconv
  haveI := hνp
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  have hβGle : (∫ z, ‖z‖ ^ 3 ∂γ) ≤ 2 * β := by
    have h1 := integral_norm_cube_gaussian_le (k := k) hk
    rw [← hγdef] at h1
    have h2 := sqrt_dim_mul_dim_le_integral_norm_cube hcov hβint
    rw [← hβdef] at h2
    linarith
  -- the smoothed indicator of `B` at width `ε`
  obtain ⟨f, hfcd, hf0, hf1, hfB, hfsupp, hfD⟩ := hC₃ B hBconv hε
  have hfbd : ∀ x, |f x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hf0 x], hf1 x⟩
  have hfint : ∀ ρ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure ρ →
      Integrable f ρ := by
    intro ρ hρ
    haveI := hρ
    exact (integrable_const (1 : ℝ)).mono' hfcd.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfbd x)
  -- the Lindeberg swap at `M = C₃/ε³`, with `(β + β_G)/√n ≤ 3q` folded in
  have herr : |(∫ x, f x ∂μ) - (∫ x, f x ∂γ)| ≤ C₃ / 2 * q / ε ^ 3 := by
    have hswap := abs_integral_smooth_sub_gaussian_le (ν := ν) hn hνp hmean hcov hβint hfcd hfbd
      (M := C₃ / ε ^ 3) (by positivity) hfD
    rw [← hμdef, ← hγdef, ← hβdef] at hswap
    refine hswap.trans ?_
    have hA : 0 ≤ C₃ / ε ^ 3 / 6 := by positivity
    have h3q : (β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ) ≤ 3 * q := by
      rw [hqdef, div_le_iff₀ hsn]
      have hcancel : 3 * (β / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 3 * β := by field_simp
      rw [hcancel]
      linarith
    calc C₃ / ε ^ 3 / 6 * (β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ)
        = C₃ / ε ^ 3 / 6 * ((β + (∫ z, ‖z‖ ^ 3 ∂γ)) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ C₃ / ε ^ 3 / 6 * (3 * q) := mul_le_mul_of_nonneg_left h3q hA
      _ = C₃ / 2 * q / ε ^ 3 := by ring
  have hthick : MeasurableSet (Metric.thickening ε B) := Metric.isOpen_thickening.measurableSet
  have hlowμ : (μ B).toReal ≤ ∫ x, f x ∂μ :=
    measureReal_le_integral_of_eq_one hBmeas (hfint μ hμprob) hf0 hfB
  have hlowγ : (γ B).toReal ≤ ∫ x, f x ∂γ :=
    measureReal_le_integral_of_eq_one hBmeas (hfint γ hγprob) hf0 hfB
  have huppμ : (∫ x, f x ∂μ) ≤ (μ (Metric.thickening ε B)).toReal :=
    integral_le_measureReal_of_support_subset hthick (hfint μ hμprob) hf1 hfsupp
  have huppγ : (∫ x, f x ∂γ) ≤ (γ (Metric.thickening ε B)).toReal :=
    integral_le_measureReal_of_support_subset hthick (hfint γ hγprob) hf1 hfsupp
  have hswap' := abs_le.1 herr
  constructor
  · linarith [hswap'.2, hlowμ, huppγ]
  · linarith [hswap'.1, hlowγ, huppμ]

/-! #### The convex headline -/

/-- `toReal` transfer for an `ℝ≥0∞` bound of the shape `a ≤ b + ofReal r`. -/
private lemma toReal_le_add_of_le_add_ofReal {a b : ℝ≥0∞} {r : ℝ}
    (hb : b ≠ ⊤) (hr : 0 ≤ r) (h : a ≤ b + ENNReal.ofReal r) :
    a.toReal ≤ b.toReal + r := by
  have hfin : b + ENNReal.ofReal r ≠ ⊤ := by
    simp [ENNReal.add_ne_top, hb]
  have h2 := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr] at h2

/-- **Elementary convex-set Berry–Esseen bound (honest, non-sharp).** For every dimension `k > 0`
there is a constant `C` such that for all `n > 0`, every centred identity-covariance law `ν` with
finite third moment `β = ∫‖y‖³ dν`, and every measurable convex `B`,

`|μₙ(B) − γ(B)| ≤ C (β/√n)^{1/4}`,

where `μₙ` is the law of `n^{-1/2} ∑ᵢ Yᵢ` and `γ = N(0, I_k)`.

This is the strongest bound the elementary "smooth the indicator + Lindeberg swap" route yields.
Optimising `ε` in `ε^{-3} β/√n + C ε` balances steps 2–3 at `ε = (β/√n)^{1/4}`, giving an error of
order `(β/√n)^{1/4} = n^{-1/8}` — **not** the `n^{-1/2}` rate of the frozen
`bentkus_berry_esseen_convex`. The constant also carries a dimension factor: it is
`C = C₀ + C_k` with `C₀` the third-derivative constant of `exists_smoothed_convex_indicator` and
`C_k = gaussianShellConst k = 8k^{3/2}/√(2π)` the Gaussian boundary-shell constant. Both deviations
are intrinsic to the mollifier method; the sharp `400 k^{1/4} · β/√n` needs Bentkus's Fourier
analysis and is not attempted. (Ball's theorem gives the sharp shell constant `4 k^{1/4}`, which is
exactly the dimension factor of Bentkus's bound; only *finiteness* at fixed `k` is needed here, and
that is what `GaussianShell` proves elementarily.)

**Proof.** `berryEsseen_convex_levy_elementary` at width `ε := (β/√n)^{1/4}` gives, for every
measurable convex `A`, both `μₙ(A) ≤ γ(Aᵋ) + C₀ ε` and `γ(A) ≤ μₙ(Aᵋ) + C₀ ε` (the balance
`(β/√n)/ε³ = ε` is `hbal` below). Applying the first to `A := B` and collapsing the thickening by
`gaussian_thickening_le` bounds `μₙ(B) − γ(B)`. For the reverse deviation one cannot thicken `μₙ`
— it is not Gaussian — so the second inequality is applied instead to the *erosion*
`A := erosion ε B`, which is open and convex (`isOpen_erosion`, `convex_erosion`) and whose
`ε`-thickening sits inside `B` (`thickening_erosion_subset`); `gaussian_le_erosion_add` then
converts `γ(erosion ε B)` back to `γ(B)`. -/
theorem berryEsseen_convex_elementary {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k)))
      (B : Set (EuclideanSpace ℝ (Fin k))),
      0 < n → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν → MeasurableSet B → Convex ℝ B →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₀, hC₀pos, hlevy⟩ := berryEsseen_convex_levy_elementary hk
  have hCkpos : 0 < gaussianShellConst k := gaussianShellConst_pos hk
  refine ⟨C₀ + gaussianShellConst k, by linarith, ?_⟩
  intro n ν B hn hνp hmean hcov hβint hBmeas hBconv
  haveI := hνp
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := multivariateGaussian 0 1 with hγdef
  set μ : Measure (EuclideanSpace ℝ (Fin k)) :=
    (Measure.pi fun _ : Fin n => ν).map (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) with hμdef
  haveI hγprob : IsProbabilityMeasure γ := by rw [hγdef]; infer_instance
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [hμdef]; exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  set β : ℝ := ∫ y, ‖y‖ ^ 3 ∂ν with hβdef
  have hβpos : 0 < β := integral_norm_cube_pos hk hcov hβint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  set q : ℝ := β / Real.sqrt (n : ℝ) with hqdef
  have hqpos : 0 < q := div_pos hβpos hsn
  -- the balancing width `ε = q^{1/4}`, at which `q/ε³ = ε`
  have hεpos : 0 < q ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hqpos _
  have hbal : q / (q ^ ((1 : ℝ) / 4)) ^ 3 = q ^ ((1 : ℝ) / 4) := by
    have hcube : (q ^ ((1 : ℝ) / 4)) ^ 3 = q ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (q ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hqpos.le]
      norm_num
    have hsum : q ^ ((1 : ℝ) / 4) * q ^ ((3 : ℝ) / 4) = q := by
      rw [← Real.rpow_add hqpos]
      norm_num
    rw [hcube, div_eq_iff (Real.rpow_pos_of_pos hqpos _).ne']
    exact hsum.symm
  have hC₀bal : C₀ * q / (q ^ ((1 : ℝ) / 4)) ^ 3 = C₀ * q ^ ((1 : ℝ) / 4) := by
    rw [mul_div_assoc, hbal]
  -- the Lévy form at `B` itself, and at its erosion
  have hlevyB := hlevy n ν B (q ^ ((1 : ℝ) / 4)) hn hεpos hνp hmean hcov hβint hBmeas hBconv
  rw [← hμdef, ← hβdef, ← hqdef, hC₀bal] at hlevyB
  have hEmeas : MeasurableSet (erosion (q ^ ((1 : ℝ) / 4)) B) :=
    (isOpen_erosion _ B).measurableSet
  have hEconv : Convex ℝ (erosion (q ^ ((1 : ℝ) / 4)) B) := convex_erosion hBconv
  have hlevyE := hlevy n ν (erosion (q ^ ((1 : ℝ) / 4)) B) (q ^ ((1 : ℝ) / 4)) hn hεpos hνp
    hmean hcov hβint hEmeas hEconv
  rw [← hμdef, ← hβdef, ← hqdef, hC₀bal] at hlevyE
  -- the two shell collapses
  have hthick : (γ (Metric.thickening (q ^ ((1 : ℝ) / 4)) B)).toReal
      ≤ (γ B).toReal + gaussianShellConst k * q ^ ((1 : ℝ) / 4) := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_thickening_le hk hBconv hεpos
    rwa [← hγdef] at this
  have herode : (γ B).toReal
      ≤ (γ (erosion (q ^ ((1 : ℝ) / 4)) B)).toReal + gaussianShellConst k * q ^ ((1 : ℝ) / 4) := by
    refine toReal_le_add_of_le_add_ofReal (measure_ne_top _ _) (by positivity) ?_
    have := gaussian_le_erosion_add hk hBmeas hBconv hεpos
    rwa [← hγdef] at this
  -- the erosion's thickening sits inside `B`, so `μ` can be pushed back without a shell bound
  have hback : (μ (Metric.thickening (q ^ ((1 : ℝ) / 4)) (erosion (q ^ ((1 : ℝ) / 4)) B))).toReal
      ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (thickening_erosion_subset _ B))
  rw [abs_sub_le_iff]
  constructor
  · linarith [hlevyB.1]
  · linarith [hlevyE.2]

end ElementaryRoute

end StatLean.HypothesisTesting
