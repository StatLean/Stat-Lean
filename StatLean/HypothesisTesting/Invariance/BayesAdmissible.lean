import StatLean.HypothesisTesting.Invariance.Admissibility
import StatLean.Bayesian.Conjugacy.NormalNormal
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Admissibility via unique Bayes solutions, and the Gaussian scale-mixture device

A general decision-theoretic route to admissibility is to exhibit a procedure as the
**unique Bayes solution** of some prior problem. For testing, the prior problem is a pair
of priors — one carried by the null class, one by the alternative class — under 0–1 loss.
Averaging the two families produces two mixture densities
$$ h_i(x) \;=\; \int f_\theta(x)\,d\Lambda_i(\theta), \qquad i = 0, 1, $$
and the Bayes test rejects where `h₁ ≥ k h₀`. This is a Neyman–Pearson test for the simple
problem `h₀` versus `h₁`; when the boundary `{h₁ = k h₀}` is null, that test is unique, and
uniqueness upgrades directly to admissibility of the original test. If moreover the prior
on the null class concentrates on the parameters where the size `α` is attained, the
sharper `α`-admissibility follows. Everything applies verbatim to any subclass of
alternatives carrying the alternative prior.

The second half of the file records the device that makes the method work in normal
problems with **nuisance means**. A Gaussian location family with a fixed variance `σ²`,
mixed over its mean by a suitable prior, reproduces a centred Gaussian of any larger
variance `M²`; choosing `M²` above all the variances in play makes the contribution of the
nuisance means to the likelihood ratio cancel, so that the ratio reduces to the one
computed with the means known.

**Main results.**
* `mixtureDensity`, `bayesTest` — the two-prior mixture densities and the nonrandomized
  Bayes test;
* `bayesTest_isDAdmissible`, `bayesTest_isAlphaAdmissible` — admissibility of the Bayes
  test against the alternative class;
* `bayesTest_admissible_of_subset` — the same conclusions against any subclass carrying
  the alternative prior;
* `exists_gaussian_scale_mixture` — the mixing identity producing a centred Gaussian of
  prescribed larger variance.

**Proof formalization notes.**
* The boundary condition is written division-free as `μ {x | h₁ x = k * h₀ x} = 0`; with
  the `θ`-free support hypothesis this is the same as the vanishing of the set where the
  likelihood ratio equals `k`, and it avoids junk values of division.
* The support hypothesis (`hsupp`) is the source's "the set `{x : f_θ(x) > 0}` does not
  depend on `θ`"; the joint measurability of `(θ, x) ↦ f_θ(x)` is what makes the mixture
  densities measurable.
* The priors are probability measures on the parameter space with `Λ₀` carried by the null
  class and `Λ₁` by the alternative class, transcribing `Λ₀(Θ_H) = Λ₁(Θ_K) = 1`.
* `bayesTest` is nonrandomized by construction, matching the source: randomized
  competitors are allowed, but the Bayes test itself must be an indicator for the
  uniqueness argument to apply.
* `exists_gaussian_scale_mixture` is stated in two equivalent readings: the pointwise
  density identity of the source, and the measure-level mixture identity. The intended
  tool for the construction (the mixing prior is itself centred Gaussian, of variance
  `M² − σ²`) is the normal–normal conjugacy already developed in `StatLean.Bayesian`.
* Positivity `σ² ≠ 0` is required for the Gaussian density to be the nondegenerate one;
  the source's `σ²` is a genuine variance.

**Bibliographic comments.** Exhibiting a test as a unique Bayes solution as a route to
admissibility, and the limiting-prior technique behind the normal examples, are due to
C. Stein ("The admissibility of Hotelling's $T^2$-test," *Ann. Math. Statist.* **27**
(1956), 616–623) and A. Birnbaum ("Characterizations of complete classes of tests of some
multiparametric hypotheses, with applications to likelihood ratio tests," *Ann. Math.
Statist.* **26** (1955), 21–36); the corresponding complete-class results for the
multivariate exponential family are due to K. Matthes and D. R. Truax ("Tests of composite
hypotheses for the multivariate exponential family," *Ann. Math. Statist.* **38** (1967),
681–697). The admissibility of the one- and two-sided $t$-tests against all invariant
classes of alternatives, obtained by approximating the improper uniform prior on
$\log\sigma$, is due to E. L. Lehmann and C. Stein (1953), extending their earlier joint
work (*Ann. Math. Statist.* **20** (1949), 28–45). The underlying optimality criterion is
that of J. Neyman and E. S. Pearson (*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-! ## The two-prior Bayes test -/

section Bayes

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Θ]

/-- The **mixture density** of a dominated family against a prior:
`h(x) = ∫ f_θ(x) dΛ(θ)`. -/
noncomputable def mixtureDensity (f : Θ → 𝓧 → ℝ) (Λ : Measure Θ) (x : 𝓧) : ℝ :=
  ∫ θ, f θ x ∂Λ

/-- The **nonrandomized Bayes test** for the two-prior 0–1-loss problem with threshold
`k`: reject exactly where the alternative mixture density is at least `k` times the null
mixture density. -/
noncomputable def bayesTest (h₀ h₁ : 𝓧 → ℝ) (k : ℝ) : 𝓧 → ℝ :=
  fun x => if k * h₀ x ≤ h₁ x then 1 else 0

/-- **A Bayes test with null boundary is d-admissible.** -/
theorem bayesTest_isDAdmissible {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K : Set Θ} {k : ℝ}
    -- USER-INPUT: the model is dominated by `μ` with densities `f`, jointly measurable
    -- in parameter and observation
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the null and alternative classes are measurable
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K)
    -- USER-INPUT: the priors are carried by the null and alternative classes
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ_K = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0) :
    IsDAdmissible P Θ_H Θ_K
      (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  sorry

/-- **A Bayes test whose null prior concentrates on the size-attaining parameters is
`α`-admissible.** -/
theorem bayesTest_isAlphaAdmissible {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K : Set Θ} {k α : ℝ}
    -- USER-INPUT: dominated model with jointly measurable nonnegative densities
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the null and alternative classes are measurable
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K)
    -- USER-INPUT: the priors are carried by the null and alternative classes
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ_K = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    -- USER-INPUT: `α` is the size of the Bayes test on the null class
    (hlevel : IsLevel P Θ_H (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) α)
    -- USER-INPUT: the null prior concentrates on the parameters where the size is attained
    (hω : Λ₀ {θ ∈ Θ_H |
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ = α} = 1) :
    IsAlphaAdmissible P Θ_H Θ_K α
      (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  sorry

/-- **Admissibility against any subclass carrying the alternative prior.** If `Λ₁` gives
probability one to a subclass `Θ'` of the alternatives, both conclusions hold with `Θ'` in
place of the full alternative class. -/
theorem bayesTest_admissible_of_subset {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {f : Θ → 𝓧 → ℝ} {Λ₀ Λ₁ : Measure Θ}
    [IsProbabilityMeasure Λ₀] [IsProbabilityMeasure Λ₁] {Θ_H Θ_K Θ' : Set Θ} {k α : ℝ}
    -- USER-INPUT: dominated model with jointly measurable nonnegative densities
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (f θ x))
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    (hfnonneg : ∀ θ x, 0 ≤ f θ x)
    -- USER-INPUT: the support of the density does not depend on the parameter
    (hsupp : ∀ (θ θ' : Θ) (x : 𝓧), 0 < f θ x ↔ 0 < f θ' x)
    -- USER-INPUT: the classes are measurable and `Θ'` is a subclass of the alternatives
    (hΘH : MeasurableSet Θ_H) (hΘK : MeasurableSet Θ_K) (hΘ' : MeasurableSet Θ')
    (hsub : Θ' ⊆ Θ_K)
    -- USER-INPUT: the priors are carried by the null class and by the subclass
    (hΛ₀ : Λ₀ Θ_H = 1) (hΛ₁ : Λ₁ Θ' = 1)
    -- USER-INPUT: the Bayes boundary is null
    (hbdry : μ {x | mixtureDensity f Λ₁ x = k * mixtureDensity f Λ₀ x} = 0)
    -- USER-INPUT: `α` is the size of the Bayes test, attained `Λ₀`-almost surely
    (hlevel : IsLevel P Θ_H (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) α)
    (hω : Λ₀ {θ ∈ Θ_H |
      power P (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) θ = α} = 1) :
    IsDAdmissible P Θ_H Θ'
        (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) ∧
      IsAlphaAdmissible P Θ_H Θ' α
        (bayesTest (mixtureDensity f Λ₀) (mixtureDensity f Λ₁) k) := by
  sorry

end Bayes

/-! ## The Gaussian scale-mixture identity -/

open StatLean.Bayesian in
/-- The Gaussian known-variance kernel evaluated at `m'` is the Gaussian law `N(m', v)`
(re-derivation of the private `gaussKernel_apply_eq` for use here). -/
private theorem gaussKernel_apply_eq' {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) :
    gaussKernel v m' = gaussianReal m' v := by
  have hmeas : Measurable (Function.uncurry fun θ x => gaussianPDF θ v x) := by
    change Measurable fun z : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal z.1 v z.2)
    refine Measurable.ennreal_ofReal ?_
    unfold gaussianPDFReal
    fun_prop
  rw [gaussKernel, Kernel.withDensity_apply _ hmeas, Kernel.const_apply,
    gaussianReal_of_var_ne_zero _ hv]

/-- **Mixing a Gaussian location family over its mean reproduces a wider centred
Gaussian.** For a variance `σ² > 0` and any larger `M²`, there is a prior on the mean
under which the mixture of `N(ζ, σ²)` over `ζ` is exactly `N(0, M²)` — stated both as the
pointwise density identity and as the measure-level mixture identity.

This is the device that removes nuisance means from a likelihood ratio: choosing `M²`
above every variance in play makes the mean contributions to the two mixture densities
cancel. The intended construction takes the mixing prior itself centred Gaussian with
variance `M² − σ²`, for which the normal–normal conjugacy of `StatLean.Bayesian` supplies
the computation. -/
theorem exists_gaussian_scale_mixture {σ2 M2 : NNReal}
    -- USER-INPUT: the inner variance is nondegenerate
    (hσ : σ2 ≠ 0)
    -- USER-INPUT: the target variance is strictly larger
    (hσM : σ2 < M2) :
    ∃ Λ : Measure ℝ, IsProbabilityMeasure Λ ∧
      (∀ z : ℝ, ∫ ζ, gaussianPDFReal ζ σ2 z ∂Λ = gaussianPDFReal 0 M2 z) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        ∫⁻ ζ, gaussianReal ζ σ2 B ∂Λ = gaussianReal 0 M2 B) := by
  classical
  have hM2pos : (0 : NNReal) < M2 := lt_of_le_of_lt (zero_le _) hσM
  have hM2 : M2 ≠ 0 := hM2pos.ne'
  -- The measure-level mixture identity, via the Gaussian convolution kernel.
  have hkey : ∀ B : Set ℝ, MeasurableSet B →
      ∫⁻ ζ, gaussianReal ζ σ2 B ∂(gaussianReal 0 (M2 - σ2)) = gaussianReal 0 M2 B := by
    intro B hB
    haveI hmark := StatLean.Bayesian.isMarkovKernel_gaussKernel hσ
    have key : StatLean.Bayesian.gaussKernel σ2 ∘ₘ gaussianReal 0 (M2 - σ2)
        = gaussianReal 0 M2 := by
      rw [StatLean.Bayesian.comp_gaussKernel_gaussianReal hσ, tsub_add_cancel_of_le hσM.le]
    calc ∫⁻ ζ, gaussianReal ζ σ2 B ∂(gaussianReal 0 (M2 - σ2))
        = ∫⁻ ζ, StatLean.Bayesian.gaussKernel σ2 ζ B ∂(gaussianReal 0 (M2 - σ2)) := by
          refine lintegral_congr fun ζ => ?_
          rw [gaussKernel_apply_eq' hσ]
      _ = (StatLean.Bayesian.gaussKernel σ2 ∘ₘ gaussianReal 0 (M2 - σ2)) B :=
          (Measure.bind_apply hB (Kernel.measurable _).aemeasurable).symm
      _ = gaussianReal 0 M2 B := by rw [key]
  refine ⟨gaussianReal 0 (M2 - σ2), inferInstance, ?_, hkey⟩
  -- Pointwise density identity, obtained from `hkey` by density uniqueness + continuity.
  -- Joint measurability of `(w, ζ) ↦ gaussianPDF ζ σ2 w`.
  have hjm : Measurable (Function.uncurry fun w ζ => gaussianPDF ζ σ2 w) := by
    change Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal p.2 σ2 p.1)
    refine Measurable.ennreal_ofReal ?_
    unfold gaussianPDFReal
    fun_prop
  have hLmeas : Measurable
      fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)) :=
    hjm.lintegral_prod_right (ν := gaussianReal 0 (M2 - σ2))
  -- The mixture measure has marginal density `w ↦ ∫⁻ ζ, gaussianPDF ζ σ2 w ∂Λ`.
  have hwd : (volume : Measure ℝ).withDensity
      (fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)))
      = gaussianReal 0 M2 := by
    ext B hB
    rw [withDensity_apply _ hB, ← hkey B hB,
      lintegral_lintegral_swap (μ := volume.restrict B)
        (ν := gaussianReal 0 (M2 - σ2)) hjm.aemeasurable]
    refine lintegral_congr fun ζ => ?_
    rw [gaussianReal_of_var_ne_zero ζ hσ, withDensity_apply _ hB]
  -- Density uniqueness gives the a.e. identity at the `ℝ≥0∞` level.
  have hae : (fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)))
      =ᵐ[volume] gaussianPDF 0 M2 := by
    have h1 : (volume : Measure ℝ).withDensity
        (fun w => ∫⁻ ζ, gaussianPDF ζ σ2 w ∂(gaussianReal 0 (M2 - σ2)))
        = (volume : Measure ℝ).withDensity (gaussianPDF 0 M2) := by
      rw [hwd, gaussianReal_of_var_ne_zero 0 hM2]
    exact (withDensity_eq_iff_of_sigmaFinite hLmeas.aemeasurable
      (measurable_gaussianPDF 0 M2).aemeasurable).mp h1
  -- The Bochner density is the `toReal` of the `ℝ≥0∞` one.
  have hdL : ∀ z, ∫ ζ, gaussianPDFReal ζ σ2 z ∂(gaussianReal 0 (M2 - σ2))
      = (∫⁻ ζ, gaussianPDF ζ σ2 z ∂(gaussianReal 0 (M2 - σ2))).toReal := by
    intro z
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ζ => gaussianPDFReal_nonneg ζ σ2 z)
      (Continuous.aestronglyMeasurable (by unfold gaussianPDFReal; fun_prop))]
    rfl
  -- Transport the a.e. identity to the real level.
  have hae_real : (fun z => ∫ ζ, gaussianPDFReal ζ σ2 z ∂(gaussianReal 0 (M2 - σ2)))
      =ᵐ[volume] fun z => gaussianPDFReal 0 M2 z := by
    filter_upwards [hae] with z hz
    rw [hdL z, hz, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 M2 z)]
  -- Both densities are continuous, so a.e. equality upgrades to everywhere.
  have hcont_g : Continuous fun z => gaussianPDFReal 0 M2 z := by
    unfold gaussianPDFReal; fun_prop
  have hcont_d : Continuous
      fun z => ∫ ζ, gaussianPDFReal ζ σ2 z ∂(gaussianReal 0 (M2 - σ2)) := by
    refine continuous_of_dominated (bound := fun _ => (Real.sqrt (2 * Real.pi * σ2))⁻¹)
      (fun z => ?_) (fun z => ?_) (integrable_const _) (ae_of_all _ fun ζ => ?_)
    · exact (Continuous.aestronglyMeasurable (by unfold gaussianPDFReal; fun_prop))
    · refine ae_of_all _ fun ζ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg ζ σ2 z)]
      calc gaussianPDFReal ζ σ2 z
          = (Real.sqrt (2 * Real.pi * σ2))⁻¹ * Real.exp (-(z - ζ) ^ 2 / (2 * σ2)) := rfl
        _ ≤ (Real.sqrt (2 * Real.pi * σ2))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by
                rw [div_nonpos_iff]
                exact Or.inr ⟨neg_nonpos.mpr (sq_nonneg _), by positivity⟩))
              (by positivity)
        _ = (Real.sqrt (2 * Real.pi * σ2))⁻¹ := mul_one _
    · unfold gaussianPDFReal; fun_prop
  exact fun z => congrFun (Measure.eq_of_ae_eq hae_real hcont_d hcont_g) z

end StatLean.HypothesisTesting
