import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A multivariate Berry–Esseen bound via Lindeberg swapping (honest, non-sharp)

This file develops the elementary "smooth the indicator + Lindeberg swap" route to a
multivariate Berry–Esseen bound, as suggested for
`StatLean.HypothesisTesting.GoodnessOfFit.SmoothTestLargeK`. The two statements quoted
there, `bentkus_berry_esseen_convex` (constant `400 k^{1/4}`) and
`bentkus_berry_esseen_ball` (dimension-free `C`), are **Bentkus (2003)**: a sharp,
research-level dimension factor obtained by Fourier analysis over convex bodies. They are
*not* reproduced here and are left sorried in that file.

What this file records instead is the strongest bound the elementary route yields *honestly*.
The single ingredient that is proved unconditionally and is genuinely dimension-free is the
**Gaussian slab (half-space) anti-concentration** bound:

`gaussian_slab_measure_le` — for a unit vector `u` and `a ≤ b`,
`N(0, I_k)({z : a < ⟪u,z⟫ ≤ b}) ≤ (b - a) / √(2π)`,

whose constant `1/√(2π)` carries **no dimension factor at all**. This is "step 3" of the
route for a half-space, and it is the one-dimensional marginal statement: the projection
`z ↦ ⟪u,z⟫` of `N(0,I_k)` is exactly `N(0,1)`, whose density is bounded by `1/√(2π)`.

## Honest accounting of the elementary route (see the module docstring below for the report)

The remaining two ingredients — the smoothed convex indicator with third-derivative bounds
(`ContDiffBump` convolution) and the third-order multivariate Lindeberg swap — are recorded
as **named `private` lemmas carrying a `sorry` and a precise `TODO`**; Mathlib v4.29.1 has no
multivariate Taylor remainder bound, which is the analytic obstruction. Crucially, even once
those are filled, the elementary balance of steps 2–3 does **not** reach the `β/√n` *rate* of
the frozen statements: optimising `ε` in `ε^{-3} β/√n + C ε` gives an error of order
`(β/√n)^{1/4}`, i.e. `n^{-1/8}`, not `n^{-1/2}`. That is a genuine feature of the mollifier
method (the sharp rate needs characteristic functions / Esseen's smoothing lemma), and it is
reported precisely rather than papered over.

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

/-! ### The remaining ingredients of the elementary route (planned debt)

The two analytic bricks below are the pieces of the Lindeberg-swap route that are *not*
proved here. Each is a **true** statement (recorded as named `private` planned debt, per the
project charter), and each is blocked on a specific Mathlib gap, stated in its `TODO`. They
are deliberately *not* assembled into a `sorry`-free theorem: the honest final bound
`berryEsseen_convex_elementary` records the exact statement the route delivers, and its
exponent `(β/√n)^{1/4}` is the genuine — non-sharp — outcome (see the module docstring). -/

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

/-- **[Planned debt]** Smoothed convex indicator with controlled third derivative.
In each dimension `k` there is a constant `C₃` (quantified *before* `B` and `ε`, so the bound
is not vacuous) such that every convex `B` and width `ε > 0` admit a smooth `f : ℝ^k → [0,1]`
equal to `1` on `B`, supported inside the `ε`-thickening of `B`, with `‖D³f‖ ≤ C₃ / ε³`.

TODO: convolve the indicator of the `(ε/2)`-thickening with `(ContDiffBump …).normed` of
radius `ε/2`; then `C₃ = ‖D³ φ‖_{L¹(ℝ^k)}` (dimension-dependent — this is one source of the
`k`-factor in `berryEsseen_convex_elementary`). Uses `ContDiffBump.contDiff_normed` and
`convolution` derivative bounds. -/
private lemma exists_smoothed_convex_indicator (k : ℕ) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ B : Set (EuclideanSpace ℝ (Fin k)), Convex ℝ B → ∀ {ε : ℝ}, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x ∈ B, f x = 1) ∧ (∀ x, f x ≠ 0 → x ∈ Metric.thickening ε B) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) := by
  -- TODO (planned debt): ContDiffBump convolution; see docstring.
  sorry

/-- **[Planned debt — dimension-free norm derivative bounds absent from Mathlib v4.29.1]**
Smoothed **radial** indicator with an *absolute* (dimension-free) third-derivative constant.
There is a constant `C₃` (independent of the dimension `k`, the radius `a` and the width `ε`)
such that for every ball `{‖z‖ ≤ a}` with `0 ≤ a` and every width `0 < ε ≤ a` there is a smooth
`f : ℝ^k → [0,1]`, equal to `1` on `{‖z‖ ≤ a}`, vanishing on `{‖z‖ > a + ε}`, with
`‖D³f‖ ≤ C₃ / ε³`. This is the radial analogue of `exists_smoothed_convex_indicator`, and unlike
the convex one its constant is genuinely dimension-free, because it is built from a
*one-dimensional* cutoff composed with the norm.

Construction: `f = χ ∘ ‖·‖`, where `χ : ℝ → [0,1]` is a fixed smooth cutoff with `χ = 1` on
`(-∞, a]`, `χ = 0` on `[a + ε, ∞)` and `‖χ⁽ʲ⁾‖ ≤ Bⱼ ε⁻ʲ` (e.g.
`1 - Real.smoothTransition ((· - a)/ε)`, whose derivatives are bounded by absolute constants
`Bⱼ` since `smoothTransition` is constant off
`[0,1]`). Since `a > 0`, `f ≡ 1` on a neighbourhood of `0`, so the non-smoothness of `‖·‖` at the
origin is invisible and `f` is globally `C³`. The third-derivative bound is Faà di Bruno
(`norm_iteratedFDeriv_comp_le`): on the support `‖z‖ ∈ [a, a+ε]` one has `‖Dⁱ‖·‖‖ ≤ cᵢ ‖z‖^{1-i}`
with **dimension-free** `cᵢ` (`‖D‖·‖‖ = 1`, `‖D²‖·‖‖ ≲ ‖z‖⁻¹`, `‖D³‖·‖‖ ≲ ‖z‖⁻²`), and combining
with `‖χ⁽ʲ⁾‖ ≤ Bⱼ ε⁻ʲ` and `‖z‖ ≥ a ≥ ε` gives `‖D³f‖ ≤ C₃ ε⁻³` with `C₃` absolute.

TODO: the two missing quantitative bricks are (i) an explicit `∀ x, |smoothTransition⁽ʲ⁾ x| ≤ Bⱼ`
(provable from `smoothTransition` constant off `[0,1]` + continuity on the compact `[0,1]`), and
(ii) **dimension-free iterated-derivative bounds for the Euclidean norm away from `0`**,
`‖iteratedFDeriv ℝ i (‖·‖) z‖ ≤ cᵢ ‖z‖^{1-i}` for `‖z‖ > 0`, which Mathlib v4.29.1 does not
provide (it has `contDiffAt_norm`/smoothness away from `0` but no quantitative iterated bounds).
The hypothesis `ε ≤ a` records honestly that the elementary `χ ∘ ‖·‖` route yields a
dimension-free, `a`-uniform `C₃` only for `ε ≤ a`; for tiny balls (`ε > a`) the norm's second
derivative `≈ ‖z‖⁻¹` is not controlled by `ε⁻¹`, which is exactly the small-radius gap the ball
assembly `berryEsseen_ball_elementary` handles separately. -/
private lemma exists_smoothed_radial_indicator :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (k : ℕ) (a : ℝ), 0 ≤ a → ∀ {ε : ℝ}, 0 < ε → ε ≤ a →
      ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        ContDiff ℝ 3 f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a → f x = 1) ∧ (∀ x, a + ε < ‖x‖ → f x = 0) ∧
        (∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C₃ / ε ^ 3) := by
  -- TODO (planned debt): 1-D cutoff composed with the norm; see docstring.
  sorry

/-- **[Planned debt]** Lindeberg smooth-function comparison for the normalized sum.
For a *fixed* `C³` test function `f` with `‖D³f‖ ≤ M`, replacing the `n` centred,
identity-covariance summands by Gaussians one at a time gives an error `≤ M (β + β_G) / (6√n)`,
where `β = ∫‖y‖³ dν` and `β_G = ∫‖z‖³ dN(0,I_k)`. This is `n^{-1/2}` for fixed `f`; the
degradation to `n^{-1/8}` for *sets* comes only from taking `f` a smoothed indicator with
`M ~ ε^{-3}` and optimising `ε`.

TODO: telescoping swap over the `n` independent summands (the vector-valued analogue of
`StatLean.HypothesisTesting.ForMathlib.LindebergCLT`), with the first- and second-order Taylor
terms cancelled by `hmean`/`hcov`, and the third-order term controlled by
`norm_taylor_remainder_three_le`. -/
private lemma abs_integral_smooth_sub_gaussian_le {k n : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin k))} (hn : 0 < n) (hν : IsProbabilityMeasure ν)
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) :
    |(∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i))
        - (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))|
      ≤ M / 6 * ((∫ y, ‖y‖ ^ 3 ∂ν)
          + (∫ z, ‖z‖ ^ 3 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)))
          / Real.sqrt (n : ℝ) := by
  -- TODO (planned debt): telescoping Lindeberg swap over the n summands; see docstring.
  sorry

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

TODO (planned debt): the assembly still consumes four bricks — `exists_smoothed_radial_indicator`
and `abs_integral_smooth_sub_gaussian_le` (both `sorry`, on the Mathlib gaps stated at those
lemmas), `gaussian_ball_shell_measure_le` (proved modulo the `Γ`-Stirling brick
`chiSquared_density_mul_sqrt_le`), and two elementary facts recorded here for the final assembly:
(a) `β_G := ∫‖z‖³ dN(0,I_k) ≤ 3 β` under identity covariance (via Lyapunov `β ≥ (E‖Y‖²)^{3/2} =
k^{3/2}` and the Gaussian moment `E‖G‖⁴ = k(k+2)`, giving `β_G ≤ (k(k+2))^{3/4} ≤ 3 k^{3/2}`), and
(b) `β > 0` (so `ε > 0`), again from `∫‖y‖² dν = k > 0`. The small-radius case `√t < ε`, where
`exists_smoothed_radial_indicator`'s `ε ≤ a` hypothesis fails, is handled by comparing at the
enlarged radius `ε`: `G{‖z‖ ≤ √t} ≤ G{‖z‖ ≤ ε} ≤ C_ac ε` (shell at `t = 0`) and the swap at width
`ε` bounds `μ_S{‖z‖ ≤ √t}` accordingly. None of these is blocked on new mathematics; they are
deferred only because the two principal bricks above are. -/
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
  -- TODO (planned debt): ε-optimisation assembly from the four bricks; see docstring.
  sorry

/-- **Elementary convex-set Berry–Esseen bound (honest, non-sharp).**
The strongest bound the elementary "smooth the indicator + Lindeberg swap" route yields.
Optimising `ε` in `ε^{-3} β/√n + C ε` balances steps 2–3 at `ε ~ (β/√n)^{1/4}`, giving an
error of order `(β/√n)^{1/4} = n^{-1/8}` — **not** the `n^{-1/2}` rate of the frozen
`bentkus_berry_esseen_convex`. The constant `C` also carries a dimension factor (from the
smoothed-indicator third-derivative bound `exists_smoothed_convex_indicator` and the convex
boundary covering). Both deviations are intrinsic to the mollifier method; the sharp
`400 k^{1/4} · β/√n` needs Bentkus's Fourier analysis and is not attempted.

TODO: assemble from `exists_smoothed_convex_indicator`, `abs_integral_smooth_sub_gaussian_le`
and `gaussian_slab_measure_le` (the latter, applied to a covering of `∂B^ε` by slabs, gives the
dimension factor). -/
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
  -- TODO (planned debt): optimise ε; see docstring and the three lemmas above.
  sorry

end ElementaryRoute

end StatLean.HypothesisTesting
