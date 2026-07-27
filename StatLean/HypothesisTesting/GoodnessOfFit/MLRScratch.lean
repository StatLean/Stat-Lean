import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import StatLean.AsymptoticStatistics.ForMathlib.GaussianShift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Scratch development of the noncentral chi-squared monotone-likelihood-ratio brick. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators NNReal InnerProductSpace

namespace StatLean.HypothesisTesting

section MLR

variable {k : ℕ}

/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_eucl_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Cameron–Martin shift for the standard Gaussian on `EuclideanSpace`.**  Shifting the
argument by `v` is the same as tilting by the exponential density
`exp(⟪v, z⟫ − ‖v‖²/2)`.  Transported from the `Measure.pi` form
`gaussianShift_change_of_measure` through `map_pi_eq_stdGaussian`. -/
private lemma integral_stdGaussian_shift {k : ℕ} (v : EuclideanSpace ℝ (Fin k))
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Measurable F) :
    ∫ z, F (v + z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ z, F z * Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  classical
  set a : Fin k → ℝ := fun i => v i with ha
  set π₀ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hπ₀
  have hmapT : π₀.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
    map_pi_eq_stdGaussian
  have hTmeas : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  -- transport both sides to the `Measure.pi` picture
  have hsum : ∀ u w : EuclideanSpace ℝ (Fin k), ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
    intro u w
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinner : ∀ x : Fin k → ℝ,
      ⟪v, (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))⟫_ℝ = ∑ i, a i * x i := by
    intro x
    rw [hsum]
  have hnorm : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hL : ∫ z, F (v + z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ x, F (v + WithLp.toLp 2 x) ∂π₀ := by
    rw [← hmapT, integral_map hTmeas.aemeasurable]
    exact (hF.comp (measurable_const_add v)).aestronglyMeasurable
  have hR : ∫ z, F z * Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ x, Real.exp ((∑ i, a i * x i) - (∑ i, (a i) ^ 2) / 2)
          * F (WithLp.toLp 2 x) ∂π₀ := by
    rw [← hmapT, integral_map hTmeas.aemeasurable]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [hinner x, hnorm]
      ring
    · exact (hF.mul (by fun_prop)).aestronglyMeasurable
  -- the shifted product Gaussian
  have hshift : π₀.map (fun x i => a i + x i) = Measure.pi (fun i => gaussianReal (a i) 1) := by
    haveI : ∀ i : Fin k, SigmaFinite ((gaussianReal 0 1).map (fun t : ℝ => a i + t)) := by
      intro i
      rw [gaussianReal_map_const_add]
      infer_instance
    rw [hπ₀, Measure.pi_map_pi (f := fun i (t : ℝ) => a i + t)
      (fun i => (measurable_const_add (a i)).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_add]
    simp
  have hmeasG : Measurable (fun x : Fin k → ℝ => F (WithLp.toLp 2 x)) := hF.comp hTmeas
  have hkey := gaussianShift_change_of_measure a (fun x : Fin k → ℝ => F (WithLp.toLp 2 x))
  rw [← hπ₀] at hkey
  have hstep : ∫ x, F (v + WithLp.toLp 2 x) ∂π₀
      = ∫ X, F (WithLp.toLp 2 X) ∂(Measure.pi fun i => gaussianReal (a i) 1) := by
    rw [← hshift, integral_map
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_add (a i))).aemeasurable
      hmeasG.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    congr 1
  rw [hL, hR, hstep, hkey]

/-- **1-D Gaussian Girsanov shift.**  (Same statement as the private
`ProbabilityTheory.gaussianReal_withDensity_exp_shift_1d`; repeated here because the
`Measure`-level form — not only its Bochner-integral consequence — is what the radial
argument below needs.) -/
private lemma gaussianReal_withDensity_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0),
    ← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) (by fun_prop)]
  congr 1
  ext x
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Product-form Gaussian Girsanov shift** on `ι → ℝ`. -/
private lemma pi_gaussianReal_withDensity_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
        = gaussianReal (a i) 1 :=
    fun i => gaussianReal_withDensity_shift (a i)
  haveI : ∀ i : ι, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  have hdensity : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - (a i) ^ 2 / 2)) := by
    funext y
    rw [show ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)
          = ∑ i, (a i * y i - (a i) ^ 2 / 2) from by
          rw [Finset.sum_sub_distrib, Finset.sum_div],
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  rw [hdensity, pi_withDensity_prod
    (f := fun i (x : ℝ) => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- Transport of a `withDensity` through the (measurable-equivalence) coordinate map
`WithLp.toLp 2`. -/
private lemma map_toLp_withDensity {k : ℕ} (μ : Measure (Fin k → ℝ))
    {w : (Fin k → ℝ) → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
      = (μ.map (WithLp.toLp 2)).withDensity (fun z => w z.ofLp) := by
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hw' : Measurable (fun z : EuclideanSpace ℝ (Fin k) => w z.ofLp) :=
    hw.comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))
  ext A hA
  rw [Measure.map_apply hT hA, withDensity_apply _ (hT hA), withDensity_apply _ hA,
    ← lintegral_indicator (hT hA), ← lintegral_indicator hA,
    lintegral_map (hw'.indicator hA) hT]
  classical
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator_apply, Set.mem_preimage]

/-- **Cameron–Martin identity, measure form.**  Translating the standard Gaussian on
`EuclideanSpace ℝ (Fin k)` by `v` is the same as tilting it by `exp(⟪v, ·⟫ − ‖v‖²/2)`. -/
private lemma stdGaussian_map_add_eq_withDensity {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).withDensity
          (fun z => ENNReal.ofReal (Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2))) := by
  classical
  set a : Fin k → ℝ := fun i => v i with ha
  set π₀ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hπ₀
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hmapT : π₀.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
    map_pi_eq_stdGaussian
  have hsum : ∀ u w : EuclideanSpace ℝ (Fin k), ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
    intro u w
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  have hshiftpi : π₀.map (fun x i => a i + x i) = Measure.pi (fun i => gaussianReal (a i) 1) := by
    haveI : ∀ i : Fin k, SigmaFinite ((gaussianReal 0 1).map (fun t : ℝ => a i + t)) := by
      intro i
      rw [gaussianReal_map_const_add]
      infer_instance
    rw [hπ₀, Measure.pi_map_pi (f := fun i (t : ℝ) => a i + t)
      (fun i => (measurable_const_add (a i)).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_add]
    simp
  -- left-hand side, transported to the product picture
  have hLHS : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (π₀.map (fun x i => a i + x i)).map (WithLp.toLp 2) := by
    rw [← hmapT, Measure.map_map (by fun_prop) hT,
      Measure.map_map hT
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_add (a i)))]
    congr 1
  rw [hLHS, hshiftpi, ← pi_gaussianReal_withDensity_shift a, ← hπ₀,
    map_toLp_withDensity π₀ (by fun_prop), hmapT]
  congr 1
  funext z
  rw [hsum, hnorm]


/-! ### Basic representations of the (non)central chi-squared laws -/

/-- The mean vector has length `√l`. -/
private lemma ncMean_norm {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    ‖noncentralMean k l‖ = Real.sqrt (l : ℝ) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have h2 : ‖noncentralMean k l‖ ^ 2 = (l : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hval : ∀ i : Fin k,
        (noncentralMean k l i) ^ 2 = if i = 0 then (l : ℝ) else 0 := by
      intro i
      by_cases hi : i = 0
      · simp only [noncentralMean, hi, Fin.val_zero, if_pos, if_true]
        rw [Real.sq_sqrt l.coe_nonneg]
      · have hi' : (i : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using hi
        simp [noncentralMean, hi, hi']
    simp_rw [hval]
    simp [Finset.sum_ite_eq']
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- `multivariateGaussian v 1` is the translate of the standard Gaussian by `v`. -/
private lemma mvGaussian_one_eq_map {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v 1
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- The noncentral chi-squared law as the squared-norm image of a shifted standard Gaussian. -/
private lemma ncChiSq_eq_map {k : ℕ} (l : ℝ≥0) :
    noncentralChiSquared k l
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map
          (fun z => ‖noncentralMean k l + z‖ ^ 2) := by
  rw [noncentralChiSquared, mvGaussian_one_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The central chi-squared law as the squared-norm image of the standard Gaussian. -/
private lemma chiSq_eq_map {k : ℕ} (hk : 0 < k) :
    StatLean.MultipleTesting.chiSquared k
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => ‖z‖ ^ 2) := by
  rw [← noncentralChiSquared_zero hk, ncChiSq_eq_map]
  congr 1
  funext z
  have hz : noncentralMean k (0 : ℝ≥0) = 0 := by ext i; simp [noncentralMean]
  rw [hz, zero_add]

/-- For `k ≥ 1` the standard Gaussian puts no mass at the origin. -/
private lemma stdGaussian_ne_zero_ae {k : ℕ} (hk : 0 < k) :
    ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))), z ≠ 0 := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have hzero : (stdGaussian (EuclideanSpace ℝ (Fin k))) {0} = 0 := by
    rw [← map_pi_eq_stdGaussian,
      Measure.map_apply (WithLp.measurable_toLp 2 (Fin k → ℝ)) (measurableSet_singleton _)]
    refine measure_mono_null (t := (fun x : Fin k → ℝ => x (0 : Fin k)) ⁻¹' {0}) ?_ ?_
    · intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rw [show x = (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)).ofLp from rfl, hx]
      rfl
    · rw [← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
        Measure.pi_map_eval]
      haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
      simp
  have : ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))), z ∉ ({0} : Set _) := by
    rw [ae_iff]
    simpa using hzero
  filter_upwards [this] with z hz using by simpa using hz


/-! ### The monotone likelihood ratio of the noncentral chi-squared family -/

/-- **Monotone likelihood ratio in the noncentrality parameter.**  For `k ≥ 1` the noncentral
law `χ²_k(l)` has a density with respect to the central law `χ²_k` which is a *nondecreasing*
function of its argument.

The density is produced without any recourse to the Bessel series or to the Poisson mixture
representation: by Cameron–Martin the likelihood ratio of the shifted Gaussian is
`exp(⟪ν, z⟫ − ‖ν‖²/2)`, and, the integrand `f(‖z‖²)` and the standard Gaussian both being
rotation invariant, that ratio may be replaced by its average over the sphere `‖u‖ = ‖ν‖`
— realised here as the average over the *direction* `‖y‖⁻¹ • y` of an independent Gaussian
vector `y`.  The averaged ratio depends on `z` only through `‖z‖` and, after the reflection
`y ↦ −y` turns it into an average of `cosh`, is nondecreasing in `‖z‖`. -/
private lemma exists_monotone_density {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ x, 0 ≤ g x) ∧
      (0 < l → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → g x₁ < g x₂) ∧
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ x, f x ∂(noncentralChiSquared k l)
          = ∫⁻ x, f x * ENNReal.ofReal (g x)
              ∂(StatLean.MultipleTesting.chiSquared k) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  set s : ℝ := Real.sqrt (l : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single (0 : Fin k) (1 : ℝ) with hedef
  have hene : ‖e‖ = 1 := by rw [hedef, EuclideanSpace.single, PiLp.norm_single, norm_one]
  set t : EuclideanSpace ℝ (Fin k) → ℝ := fun y => ‖y‖⁻¹ * ⟪y, e⟫_ℝ with htdef
  have htmeas : Measurable t := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_norm).inv
    · exact (continuous_id.inner continuous_const).measurable
  have htbd : ∀ y, |t y| ≤ 1 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [htdef]
    · have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
      rw [htdef]
      simp only [abs_mul, abs_inv, abs_norm]
      rw [inv_mul_le_one₀ hy0]
      calc |⟪y, e⟫_ℝ| ≤ ‖y‖ * ‖e‖ := abs_real_inner_le_norm y e
        _ = ‖y‖ := by rw [hene, mul_one]
  -- the (bounded) one-parameter family of integrands
  have hexpmeas : ∀ c : ℝ,
      Measurable (fun y : EuclideanSpace ℝ (Fin k) => Real.exp (c * t y - (l : ℝ) / 2)) :=
    fun c => (Real.continuous_exp.measurable).comp
      ((measurable_const.mul htmeas).sub measurable_const)
  have hint : ∀ c : ℝ, Integrable (fun y => Real.exp (c * t y - (l : ℝ) / 2)) γ := by
    intro c
    refine (integrable_const (Real.exp (|c| - (l : ℝ) / 2))).mono'
      (hexpmeas c).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have hbd : c * t y ≤ |c| := by
      calc c * t y ≤ |c * t y| := le_abs_self _
        _ = |c| * |t y| := abs_mul _ _
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left (htbd y) (abs_nonneg c)
        _ = |c| := mul_one _
    linarith
  have hcoshint : ∀ c : ℝ,
      Integrable (fun y => Real.cosh (c * t y) * Real.exp (-((l : ℝ) / 2))) γ := by
    intro c
    refine (integrable_const (Real.cosh |c| * Real.exp (-((l : ℝ) / 2)))).mono'
      (((Real.continuous_cosh.comp (by fun_prop : Continuous fun r : ℝ => c * r)).measurable.comp
        htmeas).mul measurable_const).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    rw [Real.cosh_le_cosh, abs_mul, abs_abs]
    calc |c| * |t y| ≤ |c| * 1 := mul_le_mul_of_nonneg_left (htbd y) (abs_nonneg c)
      _ = |c| := mul_one _
  -- the reflection `y ↦ -y` turns the exponential average into a `cosh` average
  have hneg : γ.map (fun y : EuclideanSpace ℝ (Fin k) => -y) = γ := by
    have h0 := stdGaussian_map
      (LinearIsometryEquiv.neg ℝ :
        EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    rw [hγ]
    convert h0 using 2
  have hcosh : ∀ c : ℝ,
      (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
        = ∫ y, Real.cosh (c * t y) * Real.exp (-((l : ℝ) / 2)) ∂γ := by
    intro c
    have hty : ∀ y : EuclideanSpace ℝ (Fin k), t (-y) = -(t y) := by
      intro y
      simp only [htdef, norm_neg, inner_neg_left]
      ring
    have hmirror : (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
        = ∫ y, Real.exp (-(c * t y) - (l : ℝ) / 2) ∂γ := by
      calc (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
          = ∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂(γ.map (fun y => -y)) := by rw [hneg]
        _ = ∫ y, Real.exp (c * t (-y) - (l : ℝ) / 2) ∂γ :=
            integral_map measurable_neg.aemeasurable
              (by rw [hneg]; exact (hexpmeas c).aestronglyMeasurable)
        _ = ∫ y, Real.exp (-(c * t y) - (l : ℝ) / 2) ∂γ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only []
            rw [hty y]
            ring_nf
    have hint₂ : Integrable (fun y => Real.exp (-(c * t y) - (l : ℝ) / 2)) γ := by
      have h := hint (-c)
      simpa only [neg_mul] using h
    have havg : (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
        = (1 / 2) * ((∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
            + ∫ y, Real.exp (-(c * t y) - (l : ℝ) / 2) ∂γ) := by
      rw [← hmirror]; ring
    rw [havg, ← integral_add (hint c) hint₂, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    rw [Real.cosh_eq, sub_eq_add_neg (c * t y), sub_eq_add_neg (-(c * t y)),
      Real.exp_add, Real.exp_add]
    ring
  -- the density
  set g : ℝ → ℝ := fun x => ∫ y, Real.exp (s * Real.sqrt x * t y - (l : ℝ) / 2) ∂γ with hgdef
  have hgmono : Monotone g := by
    intro x₁ x₂ hx
    have hc₁ : 0 ≤ s * Real.sqrt x₁ := by positivity
    have hc₂ : 0 ≤ s * Real.sqrt x₂ := by positivity
    rw [hgdef]
    simp only
    rw [hcosh _, hcosh _]
    refine integral_mono (hcoshint _) (hcoshint _) fun y => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul (s * Real.sqrt x₁), abs_mul (s * Real.sqrt x₂)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg hc₁, abs_of_nonneg hc₂]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) hs0
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x
    exact integral_nonneg fun y => (Real.exp_nonneg _)
  -- the direction functional is a.e. nonzero
  have htne : ∀ᵐ y ∂γ, t y ≠ 0 := by
    have hzero : γ {y : EuclideanSpace ℝ (Fin k) | ⟪y, e⟫_ℝ = 0} = 0 := by
      rw [hγ, ← map_pi_eq_stdGaussian,
        Measure.map_apply (WithLp.measurable_toLp 2 (Fin k → ℝ))
          (measurableSet_eq_fun (by fun_prop) measurable_const)]
      refine measure_mono_null (t := (fun x : Fin k → ℝ => x (0 : Fin k)) ⁻¹' {0}) ?_ ?_
      · intro x hx
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
        have hxe : ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)), e⟫_ℝ = x 0 := by
          rw [inner_eucl_sum, hedef]
          simp only [EuclideanSpace.single_apply]
          rw [Finset.sum_eq_single (0 : Fin k)]
          · simp
          · intro b _ hb
            simp [hb]
          · intro hb
            exact absurd (Finset.mem_univ (0 : Fin k)) hb
        rw [← hxe]
        exact hx
      · rw [← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
          Measure.pi_map_eval]
        haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
        simp
    have hsub : {y : EuclideanSpace ℝ (Fin k) | t y = 0}
        ⊆ {y : EuclideanSpace ℝ (Fin k) | ⟪y, e⟫_ℝ = 0} := by
      intro y hy
      simp only [Set.mem_setOf_eq, htdef] at hy ⊢
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      · have h0 : (‖y‖ : ℝ)⁻¹ ≠ 0 := by
          simp [norm_ne_zero_iff.mpr hy0]
        exact (mul_eq_zero.mp hy).resolve_left h0
    rw [ae_iff]
    refine measure_mono_null ?_ hzero
    intro y hy
    exact hsub (by simpa using hy)
  have hgstrict : 0 < l → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → g x₁ < g x₂ := by
    intro hl x₁ x₂ hx₁ hx
    have hspos : 0 < s := by
      rw [hsdef]
      exact Real.sqrt_pos.mpr (by exact_mod_cast hl)
    have hlt : s * Real.sqrt x₁ < s * Real.sqrt x₂ :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hx₁ hx) hspos
    have hc₁ : 0 ≤ s * Real.sqrt x₁ := by positivity
    set F : EuclideanSpace ℝ (Fin k) → ℝ := fun y =>
      Real.cosh (s * Real.sqrt x₂ * t y) * Real.exp (-((l : ℝ) / 2))
        - Real.cosh (s * Real.sqrt x₁ * t y) * Real.exp (-((l : ℝ) / 2)) with hF
    have hFint : Integrable F γ := (hcoshint _).sub (hcoshint _)
    have hFpos : ∀ y, t y ≠ 0 → 0 < F y := by
      intro y hty
      have habs : |s * Real.sqrt x₁ * t y| < |s * Real.sqrt x₂ * t y| := by
        rw [abs_mul (s * Real.sqrt x₁), abs_mul (s * Real.sqrt x₂),
          abs_of_nonneg hc₁, abs_of_nonneg (by positivity : (0:ℝ) ≤ s * Real.sqrt x₂)]
        exact mul_lt_mul_of_pos_right hlt (abs_pos.mpr hty)
      have := Real.cosh_lt_cosh.mpr habs
      rw [hF]
      have hexp : 0 < Real.exp (-((l : ℝ) / 2)) := Real.exp_pos _
      simp only
      nlinarith
    have hFnn : 0 ≤ᵐ[γ] F := by
      filter_upwards [htne] with y hy using (hFpos y hy).le
    have hFne : ¬ (F =ᵐ[γ] 0) := by
      intro hcon
      have hfalse : ∀ᵐ y ∂γ, False := by
        filter_upwards [hcon, htne] with y hy hty
        have h1 : 0 < F y := hFpos y hty
        rw [show F y = (0 : EuclideanSpace ℝ (Fin k) → ℝ) y from hy] at h1
        exact lt_irrefl 0 h1
      haveI : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
      have hz : γ Set.univ = 0 := by
        have h2 := ae_iff.mp hfalse
        simpa using h2
      rw [measure_univ] at hz
      exact one_ne_zero hz
    have hposint : 0 < ∫ y, F y ∂γ := by
      rcases (integral_nonneg_of_ae hFnn).lt_or_eq with hlt' | heq
      · exact hlt'
      · exact absurd ((integral_eq_zero_iff_of_nonneg_ae hFnn hFint).mp heq.symm) hFne
    have hsplit : (∫ y, F y ∂γ)
        = (∫ y, Real.cosh (s * Real.sqrt x₂ * t y) * Real.exp (-((l : ℝ) / 2)) ∂γ)
          - ∫ y, Real.cosh (s * Real.sqrt x₁ * t y) * Real.exp (-((l : ℝ) / 2)) ∂γ :=
      integral_sub (hcoshint _) (hcoshint _)
    rw [hgdef]
    simp only
    rw [hcosh _, hcosh _]
    linarith [hsplit ▸ hposint]
  refine ⟨g, hgmono, hgnn, hgstrict, ?_⟩
  intro f hf
  set ν : EuclideanSpace ℝ (Fin k) := noncentralMean k l with hνdef
  have hνnorm : ‖ν‖ = s := ncMean_norm hk l
  have hνsq : ‖ν‖ ^ 2 = (l : ℝ) := by
    rw [hνnorm, hsdef, Real.sq_sqrt l.coe_nonneg]
  set H : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun z => f (‖z‖ ^ 2) with hHdef
  have hHmeas : Measurable H := hf.comp (by fun_prop)
  -- the tilted integral as a function of the shift
  set J : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ :=
    fun u => ∫⁻ z, H z * ENNReal.ofReal (Real.exp (⟪u, z⟫_ℝ - (l : ℝ) / 2)) ∂γ with hJdef
  have hJmeas : ∀ u : EuclideanSpace ℝ (Fin k),
      Measurable (fun z => H z * ENNReal.ofReal (Real.exp (⟪u, z⟫_ℝ - (l : ℝ) / 2))) := by
    intro u
    exact hHmeas.mul (by fun_prop)
  -- (a)+(b): Cameron–Martin
  have hab : ∫⁻ x, f x ∂(noncentralChiSquared k l) = J ν := by
    rw [ncChiSq_eq_map, lintegral_map hf (by fun_prop)]
    have h1 : ∫⁻ z, f (‖ν + z‖ ^ 2) ∂γ = ∫⁻ z, H z ∂(γ.map (fun z => ν + z)) := by
      rw [lintegral_map hHmeas (by fun_prop)]
    rw [h1, hγ, stdGaussian_map_add_eq_withDensity ν,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hHmeas]
    rw [hJdef]
    refine lintegral_congr fun z => ?_
    simp only [Pi.mul_apply, hνsq]
    ring
  -- rotation invariance of `J` on spheres
  have hrot : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ = ‖ν‖ → J u = J ν := by
    intro u hu
    obtain ⟨φ, hφ⟩ : ∃ φ : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
        φ ν = u := ⟨_, Submodule.reflection_sub hu.symm⟩
    have hmapφ : γ.map (⇑φ) = γ := by rw [hγ]; exact stdGaussian_map φ
    rw [hJdef]
    simp only
    conv_lhs => rw [← hmapφ]
    rw [lintegral_map (hJmeas u) φ.continuous.measurable]
    refine lintegral_congr fun z => ?_
    have h1 : H (φ z) = H z := by rw [hHdef]; simp only [LinearIsometryEquiv.norm_map]
    have h2 : ⟪u, φ z⟫_ℝ = ⟪ν, z⟫_ℝ := by rw [← hφ]; exact φ.inner_map_map ν z
    rw [h1, h2]
  -- averaging over the direction of an independent Gaussian vector
  have hdir : ∀ᵐ y ∂γ, J (s • (‖y‖⁻¹ • y)) = J ν := by
    filter_upwards [hγ ▸ stdGaussian_ne_zero_ae hk] with y hy
    refine hrot _ ?_
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hyy : ‖(‖y‖⁻¹ • y : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hy0.ne']
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hyy, mul_one, hνnorm]
  have haverage : J ν = ∫⁻ y, J (s • (‖y‖⁻¹ • y)) ∂γ := by
    rw [lintegral_congr_ae hdir, lintegral_const]
    haveI : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
    rw [measure_univ, mul_one]
  -- the inner average is a function of `‖z‖` alone
  have hinner : ∀ z : EuclideanSpace ℝ (Fin k),
      (∫⁻ y, ENNReal.ofReal
          (Real.exp (⟪s • (‖y‖⁻¹ • y), z⟫_ℝ - (l : ℝ) / 2)) ∂γ)
        = ENNReal.ofReal (g (‖z‖ ^ 2)) := by
    intro z
    have hzz : ‖(‖z‖ • e : EuclideanSpace ℝ (Fin k))‖ = ‖z‖ := by
      rw [norm_smul, hene, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    obtain ⟨φ, hφ⟩ : ∃ φ : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
        φ (‖z‖ • e) = z := ⟨_, Submodule.reflection_sub hzz⟩
    have hmapφ : γ.map (⇑φ) = γ := by rw [hγ]; exact stdGaussian_map φ
    have hmeas0 : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal
        (Real.exp (⟪s • (‖y‖⁻¹ • y), z⟫_ℝ - (l : ℝ) / 2))) := by
      fun_prop
    conv_lhs => rw [← hmapφ]
    rw [lintegral_map hmeas0 φ.continuous.measurable]
    have hpt : ∀ y : EuclideanSpace ℝ (Fin k),
        ⟪s • (‖φ y‖⁻¹ • φ y), z⟫_ℝ = s * Real.sqrt (‖z‖ ^ 2) * t y := by
      intro y
      rw [Real.sqrt_sq (norm_nonneg z)]
      rw [real_inner_smul_left, real_inner_smul_left, LinearIsometryEquiv.norm_map]
      have hin : ⟪φ y, z⟫_ℝ = ‖z‖ * ⟪y, e⟫_ℝ := by
        conv_lhs => rw [← hφ]
        rw [φ.inner_map_map, real_inner_smul_right]
      rw [hin, htdef]
      ring
    simp_rw [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _)
      (Filter.Eventually.of_forall fun y => Real.exp_nonneg _)]
  -- assemble
  rw [hab, haverage]
  have hswap : (∫⁻ y, J (s • (‖y‖⁻¹ • y)) ∂γ)
      = ∫⁻ z, H z * ENNReal.ofReal (g (‖z‖ ^ 2)) ∂γ := by
    rw [hJdef]
    simp only
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun z => ?_
      rw [lintegral_const_mul _ (by fun_prop), hinner z]
    · refine (Measurable.aemeasurable ?_)
      exact (hHmeas.comp measurable_snd).mul (by fun_prop)
  have hfinal : ∫⁻ x, f x * ENNReal.ofReal (g x) ∂(StatLean.MultipleTesting.chiSquared k)
      = ∫⁻ z, H z * ENNReal.ofReal (g (‖z‖ ^ 2)) ∂γ := by
    rw [chiSq_eq_map hk, ← hγ]
    exact lintegral_map (hf.mul (ENNReal.measurable_ofReal.comp hgmono.measurable))
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2)
  rw [hswap, hfinal]


/-! ### Additivity in the degrees of freedom -/

/-- The noncentral chi-squared law in the product picture, for an arbitrary mean vector of
the prescribed length. -/
private lemma ncChiSq_eq_pi_map {k : ℕ} (l : ℝ≥0) {w : Fin k → ℝ}
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (l : ℝ)) :
    noncentralChiSquared k l
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, (w i + x i) ^ 2) := by
  rw [← map_normSq_multivariateGaussian_of_norm_eq k l hw, mvGaussian_one_eq_map,
    ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- `χ²₁` is the law of the square of a standard normal variable. -/
private lemma chiSq_one_eq_map :
    StatLean.MultipleTesting.chiSquared 1 = (gaussianReal 0 1).map (fun u : ℝ => u ^ 2) := by
  have hw0 : ‖(WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)) : EuclideanSpace ℝ (Fin 1))‖
      = Real.sqrt (((0 : ℝ≥0) : ℝ)) := by
    have hz : (WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)) : EuclideanSpace ℝ (Fin 1)) = 0 := by
      ext i; rfl
    rw [hz, norm_zero, NNReal.coe_zero, Real.sqrt_zero]
  have h := ncChiSq_eq_pi_map (k := 1) (l := 0) (w := fun _ => 0) hw0
  rw [noncentralChiSquared_zero one_pos] at h
  rw [h, show (fun x : Fin 1 → ℝ => ∑ i, ((0 : ℝ) + x i) ^ 2)
        = (fun u : ℝ => u ^ 2) ∘ (fun x : Fin 1 → ℝ => x 0) from by funext x; simp,
    ← Measure.map_map (by fun_prop) (by fun_prop), Measure.pi_map_eval]
  simp

/-- **Additivity of the noncentral chi-squared law in the degrees of freedom.**  `χ²_{k+1}(l)`
is the law of the sum of two independent variables, `χ²_k(l)` and `χ²₁`.  Because the
noncentrality is a complete invariant (`map_normSq_multivariateGaussian_of_norm_eq`) the mean
vector may be taken orthogonal to the split-off coordinate, which is what makes the split
carry all of the noncentrality into the `k`-dimensional factor. -/
private lemma ncChiSq_succ_eq_prod_map {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    noncentralChiSquared (k + 1) l
      = ((noncentralChiSquared k l).prod (StatLean.MultipleTesting.chiSquared 1)).map
          (fun q : ℝ × ℝ => q.1 + q.2) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  set m : Fin k → ℝ := fun j => (noncentralMean k l) j with hm
  have hmnorm : ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (l : ℝ) :=
    ncMean_norm hk l
  have hvnorm :
      ‖(WithLp.toLp 2 (Fin.cons (0 : ℝ) m) : EuclideanSpace ℝ (Fin (k + 1)))‖
        = Real.sqrt (l : ℝ) := by
    have h1 : ‖(WithLp.toLp 2 (Fin.cons (0 : ℝ) m) : EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2
        = ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      simp
    rw [← Real.sqrt_sq (norm_nonneg _), h1, hmnorm, Real.sqrt_sq (Real.sqrt_nonneg _)]
  set Qk : (Fin k → ℝ) → ℝ := fun y => ∑ j, (m j + y j) ^ 2 with hQk
  have hQkmeas : Measurable Qk := by
    refine Finset.univ.measurable_sum fun j _ => ?_
    exact (((measurable_pi_apply j : Measurable fun y : Fin k → ℝ => y j)).const_add
      (m j)).pow_const 2
  have hsqmeas : Measurable (fun u : ℝ => u ^ 2) := by fun_prop
  -- the split of the product Gaussian at the first coordinate
  have mp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => gaussianReal 0 1) (0 : Fin (k + 1))
  have hsym := mp.symm.map_eq
  have hQ : ∀ p : ℝ × (Fin k → ℝ),
      (∑ i, ((Fin.cons (0 : ℝ) m : Fin (k + 1) → ℝ) i + (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => ℝ) 0).symm p i) ^ 2) = Qk p.2 + p.1 ^ 2 := by
    intro p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, zero_add, hQk, Fin.zero_succAbove, cast_eq]
    ring
  have hsplit : noncentralChiSquared (k + 1) l
      = ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)).map
          (fun p => Qk p.2 + p.1 ^ 2) := by
    rw [ncChiSq_eq_pi_map (l := l) (w := Fin.cons (0 : ℝ) m) hvnorm, ← hsym,
      Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
    congr 1
    funext p
    simpa only [Function.comp_apply] using hQ p
  -- rearrange the product
  have hswap : ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)).map
        (fun p => Qk p.2 + p.1 ^ 2)
      = (((Measure.pi fun _ : Fin k => gaussianReal 0 1).map Qk).prod
          ((gaussianReal 0 1).map (fun u : ℝ => u ^ 2))).map (fun q : ℝ × ℝ => q.1 + q.2) := by
    rw [Measure.map_prod_map _ _ hQkmeas hsqmeas,
      Measure.map_map (by fun_prop) (hQkmeas.prodMap hsqmeas),
      ← Measure.prod_swap (μ := gaussianReal 0 1)
        (ν := Measure.pi fun _ : Fin k => gaussianReal 0 1),
      Measure.map_map (by fun_prop) measurable_swap]
    rfl
  rw [hsplit, hswap, ← ncChiSq_eq_pi_map (l := l) (w := m) hmnorm, ← chiSq_one_eq_map]

/-- **Tail form of the additivity.**  The `χ²_{k+1}(l)` upper tail is the `χ²_k(l)`-average of
the `χ²₁` upper tail at the shifted threshold. -/
private lemma ncChiSq_succ_Ioi {k : ℕ} (hk : 0 < k) (l : ℝ≥0) (c : ℝ) :
    noncentralChiSquared (k + 1) l (Set.Ioi c)
      = ∫⁻ x, StatLean.MultipleTesting.chiSquared 1 (Set.Ioi (c - x))
          ∂(noncentralChiSquared k l) := by
  rw [ncChiSq_succ_eq_prod_map hk l,
    Measure.map_apply (by fun_prop) measurableSet_Ioi,
    Measure.prod_apply ((measurable_fst.add measurable_snd) measurableSet_Ioi)]
  refine lintegral_congr fun x => ?_
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_Ioi]
  constructor <;> intro h <;> linarith


/-! ### One extra degree of freedom costs power -/

/-- **One-step degrees-of-freedom monotonicity.**  If the critical values `c₁` (for `k`) and
`c₂` (for `k+1`) are matched at the null, then the noncentral tail at `k+1` degrees of
freedom never exceeds the one at `k`.

The proof is the single-crossing argument: writing `q(x) = χ²₁(c₂ − x, ∞)` for the
conditional rejection probability of the `(k+1)`-dimensional test given the first `k`
coordinates, the difference `1_{(c₁,∞)} − q` is `≤ 0` below `c₁` and `≥ 0` above it, while
`χ²_k(l)` has a *nondecreasing* density `g` with respect to `χ²_k`
(`exists_monotone_density`); the pointwise inequality
`q·g + 1_{(c₁,∞)}·g(c₁) ≤ 1_{(c₁,∞)}·g + q·g(c₁)` then integrates to the claim, the two
`g(c₁)`-terms cancelling because the levels are matched. -/
private lemma ncChiSq_tail_succ_le {k : ℕ} (hk : 0 < k) (l : ℝ≥0) {c₁ c₂ : ℝ}
    (hlevel : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁)
      = StatLean.MultipleTesting.chiSquared (k + 1) (Set.Ioi c₂)) :
    noncentralChiSquared (k + 1) l (Set.Ioi c₂) ≤ noncentralChiSquared k l (Set.Ioi c₁) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨g, hgmono, hgnn, hgstrict, hg⟩ := exists_monotone_density hk l
  set μ : Measure ℝ := StatLean.MultipleTesting.chiSquared k with hμ
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x) with hG
  set A : ℝ≥0∞ := G c₁ with hA
  set P : ℝ → ℝ≥0∞ := Set.indicator (Set.Ioi c₁) 1 with hP
  set Q : ℝ → ℝ≥0∞ :=
    fun x => StatLean.MultipleTesting.chiSquared 1 (Set.Ioi (c₂ - x)) with hQ
  have hGmeas : Measurable G := ENNReal.measurable_ofReal.comp hgmono.measurable
  have hPmeas : Measurable P := (measurable_const : Measurable (1 : ℝ → ℝ≥0∞)).indicator
    measurableSet_Ioi
  have hQmeas : Measurable Q := by
    have hs : MeasurableSet ((fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' (Set.Ioi c₂)) :=
      (measurable_fst.add measurable_snd) measurableSet_Ioi
    have heq : Q = fun x : ℝ => StatLean.MultipleTesting.chiSquared 1
        (Prod.mk x ⁻¹' ((fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' (Set.Ioi c₂))) := by
      funext x
      simp only [hQ]
      congr 1
      ext u
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact measurable_measure_prodMk_left (ν := StatLean.MultipleTesting.chiSquared 1) hs
  have hQle : ∀ x, Q x ≤ 1 := fun x => prob_le_one
  -- the two tails as `χ²_k`-integrals of the density
  have hAval : noncentralChiSquared k l (Set.Ioi c₁) = ∫⁻ x, P x * G x ∂μ := by
    rw [← hg P hPmeas, hP, lintegral_indicator_one measurableSet_Ioi]
  have hBval : noncentralChiSquared (k + 1) l (Set.Ioi c₂) = ∫⁻ x, Q x * G x ∂μ := by
    rw [ncChiSq_succ_Ioi hk l c₂, ← hg Q hQmeas]
  -- the matched levels
  have hlev1 : ∫⁻ x, P x ∂μ = StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) := by
    rw [hP, lintegral_indicator_one measurableSet_Ioi]
  have hlev2 : ∫⁻ x, Q x ∂μ = StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) := by
    have h0 := ncChiSq_succ_Ioi hk (0 : ℝ≥0) c₂
    rw [noncentralChiSquared_zero hk, noncentralChiSquared_zero (by omega : 0 < k + 1)] at h0
    rw [hμ, ← h0, hlevel]
  -- the single-crossing pointwise inequality
  have hpt : ∀ x, Q x * G x + P x * A ≤ P x * G x + Q x * A := by
    intro x
    by_cases hx : x ∈ Set.Ioi c₁
    · have hAG : A ≤ G x := by
        refine ENNReal.ofReal_le_ofReal (hgmono ?_)
        exact le_of_lt hx
      obtain ⟨d, hd⟩ := exists_add_of_le hAG
      have hPx : P x = 1 := by rw [hP, Set.indicator_of_mem hx]; rfl
      rw [hPx, hd, one_mul, one_mul]
      have hQd : Q x * d ≤ d := by
        calc Q x * d ≤ 1 * d := mul_le_mul_right' (hQle x) d
          _ = d := one_mul d
      calc Q x * (A + d) + A = (Q x * A + A) + Q x * d := by ring
        _ ≤ (Q x * A + A) + d := by gcongr
        _ = A + d + Q x * A := by ring
    · have hGA : G x ≤ A := by
        refine ENNReal.ofReal_le_ofReal (hgmono ?_)
        simpa using hx
      have hPx : P x = 0 := by rw [hP, Set.indicator_of_notMem hx]
      rw [hPx, zero_mul, zero_mul, add_zero, zero_add]
      exact mul_le_mul_left' hGA _
  -- integrate and cancel the common finite term
  have hmain : (∫⁻ x, Q x * G x ∂μ) + (∫⁻ x, P x ∂μ) * A
      ≤ (∫⁻ x, P x * G x ∂μ) + (∫⁻ x, Q x ∂μ) * A := by
    rw [← lintegral_mul_const _ hPmeas, ← lintegral_mul_const _ hQmeas,
      ← lintegral_add_left (hQmeas.mul hGmeas), ← lintegral_add_left (hPmeas.mul hGmeas)]
    exact lintegral_mono hpt
  rw [hlev1, hlev2] at hmain
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hfin : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A ≠ ⊤ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) ?_
    rw [hA, hG]
    exact ENNReal.ofReal_ne_top
  rw [hAval, hBval]
  exact (ENNReal.add_le_add_iff_right hfin).mp hmain

end MLR

end StatLean.HypothesisTesting
