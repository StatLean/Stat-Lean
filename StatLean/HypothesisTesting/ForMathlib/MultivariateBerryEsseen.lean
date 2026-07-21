import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

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
    rw [iteratedDerivWithin_eq_iteratedDeriv hud (hgcd.contDiffAt.of_le (by exact_mod_cast hk)) hmem,
      key k hk 0]
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
