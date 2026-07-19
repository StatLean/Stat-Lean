import StatLean.PointEstimation.Equivariance.LocationMRE
import StatLean.PointEstimation.Equivariance.Pitman
import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-!
# Location equivariance — the normal example and a least-favourable property

Two results about the normal location family.

* `isLocMRE_mean_gaussian` — for independent normal observations with a common unknown
  mean and known variance, the sample mean is the minimum risk equivariant estimator
  under squared error.
* `risk_le_gaussian_of_unitVariance` — among all location families built from an
  independent sample of unit-variance observations, the minimum risk equivariant risk is
  **largest** for the normal: it is at most `1/n`, with equality in the normal case
  (`locRisk_isLocMRE_gaussian_eq`). In this sense the normal distribution is least
  favourable for equivariant location estimation.

**Reference.** Classical location-equivariant estimation; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* The least-favourable statement is proved exactly as classically, by a one-line
  comparison and *not* by a characterization theorem: the sample mean is equivariant and
  measurable and has risk `1/n` for **every** member of the class (that is just the
  variance of a mean of independent unit-variance observations), so a minimum risk
  equivariant estimator, being at least as good, has risk at most `1/n`; and in the
  normal case the sample mean is itself the minimum risk equivariant estimator, so the
  bound is attained.
* We deliberately do **not** state the converse. That for `n ≥ 3` the normal is the *only*
  member of the class attaining `1/n` is a characterization result of Kagan, Linnik and
  Rao, quoted rather than proved in the classical development; formalizing it is out of
  scope here and nothing downstream uses it.
* The sampling structure is supplied as an equation `locationBase f = Measure.pi …`
  rather than by writing out a joint density: the theorems only ever use the law, and
  this keeps the product structure available as a rewrite.
* No integrability hypotheses accompany the moment conditions: a Bochner integral of a
  non-integrable function is `0`, so `∫ t², dP₁ = 1` already forces square-integrability,
  and integrability of `t` then follows on a probability space.
* The risk `1/n` is expressed in `ℝ≥0∞` through `ENNReal.ofReal`, matching `locRisk`.

**Bibliographic comments.** Equivariant estimation of a location parameter is due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421; the admissibility of
his estimator is C. Stein, "The admissibility of Pitman's estimator of a single location
parameter," *Ann. Math. Statist.* **30** (1959), 970–979. The characterization of the
normal law by the linearity of the relevant conditional expectation — the converse
alluded to above and not formalized here — is due to A. M. Kagan, Yu. V. Linnik and
C. R. Rao, *Characterization Problems in Mathematical Statistics*, Wiley, 1973.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

section LocationExamples

variable {m : ℕ}

/-- The sample mean is measurable. -/
private lemma measurable_sampleMean :
    Measurable (fun x : Fin (m + 1) → ℝ => (∑ i, x i) / ((m : ℝ) + 1)) := by
  fun_prop

/-- The sample mean is location equivariant: `X̄(x + a𝟙) = X̄(x) + a`. -/
private lemma isLocEquivariant_sampleMean :
    IsLocEquivariant (fun x : Fin (m + 1) → ℝ => (∑ i, x i) / ((m : ℝ) + 1)) := by
  intro a x
  show (∑ i, (x + a • (1 : Fin (m + 1) → ℝ)) i) / ((m : ℝ) + 1)
    = (∑ i, x i) / ((m : ℝ) + 1) + a
  have hsum : (∑ i, (x + a • (1 : Fin (m + 1) → ℝ)) i) = (∑ i, x i) + ((m : ℝ) + 1) * a := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [hsum]
  field_simp

/-! ### The explicit product-Gaussian density and its Pitman estimator

We transfer `isLocMRE_mean_gaussian` to the explicit joint density
`gaussDensity v x = ∏ i, gaussianPDFReal 0 v (x i)`, whose `locationBase` is the product
Gaussian, and for which the Pitman estimator is the sample mean by completing the square. -/

/-- The explicit product-Gaussian density on `Fin (m + 1) → ℝ`. -/
private noncomputable def gaussDensity (v : ℝ≥0) (x : Fin (m + 1) → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 v (x i)

private lemma gaussDensity_nonneg {v : ℝ≥0} (x : Fin (m + 1) → ℝ) : 0 ≤ gaussDensity v x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _

private lemma measurable_gaussDensity (v : ℝ≥0) :
    Measurable (gaussDensity (m := m) v) := by
  unfold gaussDensity
  exact Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 v).comp
    (measurable_pi_apply i)

/-- **STEP A.** The `locationBase` of the explicit product-Gaussian density is the product
Gaussian measure. -/
private lemma locationBase_gaussDensity {v : ℝ≥0} (hv : v ≠ 0) :
    locationBase (gaussDensity (m := m) v)
      = Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 v := by
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]; infer_instance
  have h_each : (fun _ : Fin (m + 1) => gaussianReal 0 v)
      = fun _ : Fin (m + 1) => (volume : Measure ℝ).withDensity (gaussianPDF 0 v) := by
    funext _; exact gaussianReal_of_var_ne_zero 0 hv
  rw [h_each, ← MeasureTheory.pi_withDensity_prod (fun _ : Fin (m + 1) => measurable_gaussianPDF 0 v)]
  show (volume : Measure (Fin (m + 1) → ℝ)).withDensity (fun x => ENNReal.ofReal (gaussDensity v x))
    = (volume : Measure (Fin (m + 1) → ℝ)).withDensity (fun x => ∏ i, gaussianPDF 0 v (x i))
  refine withDensity_congr_ae (ae_of_all _ fun x => ?_)
  simp only [gaussDensity]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]
  rfl

/-- The variance of the sample mean, as an `ℝ≥0`: `v / (m + 1)`. -/
private noncomputable def meanVar (v : ℝ≥0) : ℝ≥0 := v / ((m : ℝ≥0) + 1)

private lemma meanVar_ne_zero {v : ℝ≥0} (hv : v ≠ 0) : meanVar (m := m) v ≠ 0 := by
  rw [meanVar, ne_eq, div_eq_zero_iff]
  push_neg
  exact ⟨hv, by positivity⟩

private lemma coe_meanVar (v : ℝ≥0) : (meanVar (m := m) v : ℝ) = (v : ℝ) / ((m : ℝ) + 1) := by
  rw [meanVar, NNReal.coe_div]
  push_cast
  ring

/-- **STEP B core.** Completing the square: the product of `m + 1` centred Gaussian slices
`x i − u` equals a `u`-independent positive constant times the density of
`𝒩(X̄, v/(m+1))` evaluated at `u`, where `X̄ = (∑ x i)/(m+1)`. -/
private lemma prod_gaussianPDFReal_sub_eq {v : ℝ≥0} (hv : v ≠ 0) (x : Fin (m + 1) → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      (∏ i, gaussianPDFReal 0 v (x i - u))
        = C * gaussianPDFReal ((∑ i, x i) / ((m : ℝ) + 1)) (meanVar v) u := by
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  set S : ℝ := ∑ i, x i with hSdef
  set X̄ : ℝ := S / N with hXbardef
  set vr : ℝ := (v : ℝ) with hvr
  have hvrpos : 0 < vr := by rw [hvr]; positivity
  set Q : ℝ := (∑ i, (x i) ^ 2) - N * X̄ ^ 2 with hQdef
  -- the product of the normalising constants times exp of the residual `Q`
  set C : ℝ := (Real.sqrt (2 * Real.pi * vr))⁻¹ ^ (m + 1)
      * Real.sqrt (2 * Real.pi * (meanVar (m := m) v : ℝ)) * Real.exp (-Q / (2 * vr)) with hCdef
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * vr) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsqrt_mv : 0 < Real.sqrt (2 * Real.pi * (meanVar (m := m) v : ℝ)) :=
    Real.sqrt_pos.mpr (by
      have : (0 : ℝ) < (meanVar (m := m) v : ℝ) := by
        rw [coe_meanVar]; positivity
      positivity)
  refine ⟨C, by rw [hCdef]; positivity, fun u => ?_⟩
  -- sum-of-squares expansion
  have hsumsq : ∑ i, (x i - u) ^ 2 = N * (u - X̄) ^ 2 + Q := by
    have hcard : (Finset.univ.card : ℝ) = N := by
      rw [Finset.card_univ, Fintype.card_fin, hNdef]; push_cast; ring
    have hexpand : ∑ i, (x i - u) ^ 2
        = (∑ i, (x i) ^ 2) - 2 * u * S + (Finset.univ.card : ℝ) * u ^ 2 := by
      rw [hSdef, Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand, hcard, hQdef, hXbardef]
    field_simp
    ring
  -- rewrite the product as a single exp
  have hprod : (∏ i, gaussianPDFReal 0 v (x i - u))
      = (Real.sqrt (2 * Real.pi * vr))⁻¹ ^ (m + 1)
        * Real.exp (-(∑ i, (x i - u) ^ 2) / (2 * vr)) := by
    simp only [gaussianPDFReal, sub_zero, hvr]
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    congr 1
    · rw [Finset.card_univ, Fintype.card_fin]
    · rw [← Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  rw [hprod, hsumsq]
  -- the target density
  have hmv : (meanVar (m := m) v : ℝ) = vr / N := by rw [coe_meanVar, hvr, hNdef]
  simp only [gaussianPDFReal]
  rw [hCdef, hmv]
  rw [neg_add, add_div, Real.exp_add]
  have h2v : (2 : ℝ) * (vr / N) = (2 * vr) / N := by ring
  rw [h2v]
  have hne : (2 * vr) ≠ 0 := by positivity
  have hNne : N ≠ 0 := hNpos.ne'
  -- match the exponentials on the `(u - X̄)²` term
  have hexp_eq : -(N * (u - X̄) ^ 2) / (2 * vr)
      = -(u - X̄) ^ 2 / ((2 * vr) / N) := by
    rw [div_div_eq_mul_div, neg_div, neg_div, div_mul_eq_mul_div]
    congr 1
    ring
  rw [hexp_eq]
  ring

/-- **The sample mean is the minimum risk equivariant estimator in the normal location
family** under squared error, for any known variance. -/
theorem isLocMRE_mean_gaussian (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    {v : ℝ≥0}
    -- USER-INPUT: the variance is known and nondegenerate
    (hv : v ≠ 0)
    -- USER-INPUT: the base member is an independent normal sample with mean `0`
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 v) :
    IsLocMRE f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1)) := by
  -- Named debt. `pitmanEstimator_isLocMRE` (in `Pitman`) is now CLOSED and axiom-clean, so
  -- the route is unblocked; what remains is the Gaussian-specific computation.
  -- Route: `IsLocMRE f ρ δ` depends on `f` only through `locationBase f` (both the risk and
  -- the equivariant class do), so transfer to the explicit density
  -- `g x = ∏ i, gaussianPDFReal 0 v (x i)` (with `locationBase g = Measure.pi (gaussianReal 0 v)`
  -- by the same `pi_withDensity_prod` argument as `AsymptoticStatistics.PiGaussian`,
  -- generalized from `v = 1`). For `g`, complete the square: `g (x − u𝟙) = C · exp(−(m+1)
  -- (u − X̄)²/(2v))` is (up to normalization) the density of `𝒩(X̄, v/(m+1))` in `u`, whence
  -- `pitmanEstimator g = X̄` by `integral_id_gaussianReal`, and `pitmanEstimator_isLocMRE g`
  -- (its Gaussian integrability/finite-risk side conditions all discharged from Gaussian
  -- moment finiteness) gives `IsLocMRE g ρ X̄`. The Gaussian first-moment/completing-the-square
  -- development is a self-contained analytic core, left as reported debt this session. The
  -- Kagan–Linnik–Rao converse is out of scope (see the docstring).
  sorry

/-- The risk of the sample mean in an independent unit-variance location family is
`1/n`, whatever the shape of the underlying distribution. This is the observation that
drives the least-favourable property of the normal law. -/
theorem locRisk_mean_eq_inv (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (P₁ : Measure ℝ) [IsProbabilityMeasure P₁]
    -- USER-INPUT: the base member is an independent sample from `P₁`
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => P₁)
    -- USER-INPUT: the coordinates are centred with unit variance
    (hmean : ∫ t, t ∂P₁ = 0) (hvar : ∫ t, t ^ 2 ∂P₁ = 1) :
    locRisk f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1))
      = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  -- Square-integrability of the coordinate law from the second-moment hypothesis.
  have hsq_int : Integrable (fun t : ℝ => t ^ 2) P₁ := by
    by_contra h; rw [integral_undef h] at hvar; exact one_ne_zero hvar.symm
  have hL2 : MemLp (fun t : ℝ => t) 2 P₁ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq_int
  -- Each coordinate is square-integrable under the product law.
  have hL2i : ∀ i : Fin (m + 1),
      MemLp (fun x : Fin (m + 1) → ℝ => x i) 2 (Measure.pi fun _ => P₁) := by
    intro i
    have := hL2.comp_measurePreserving (measurePreserving_eval (fun _ => P₁) i)
    simpa [Function.comp] using this
  have hint_i : ∀ i, Integrable (fun x : Fin (m + 1) → ℝ => x i)
      (Measure.pi fun _ => P₁) := fun i => (hL2i i).integrable one_le_two
  have hint_ij : ∀ i j, Integrable (fun x : Fin (m + 1) → ℝ => x i * x j)
      (Measure.pi fun _ => P₁) := fun i j => (hL2i i).integrable_mul (hL2i j)
  -- Coordinate first and second moments; cross moments vanish by independence.
  have hEi : ∀ i, ∫ x : Fin (m + 1) → ℝ, x i ∂(Measure.pi fun _ => P₁) = 0 := by
    intro i; rw [integral_eval]; exact hmean
  have hindep : iIndepFun (fun i (x : Fin (m + 1) → ℝ) => x i) (Measure.pi fun _ => P₁) :=
    iIndepFun_pi fun _ => aemeasurable_id
  have hc : ∀ i j, ∫ x : Fin (m + 1) → ℝ, x i * x j ∂(Measure.pi fun _ => P₁)
      = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have heq : (fun x : Fin (m + 1) → ℝ => x i * x i)
          = fun x => (fun t : ℝ => t ^ 2) (x i) := by funext x; ring
      have hev := integral_comp_eval (μ := fun _ : Fin (m + 1) => P₁) (i := i)
        (f := fun t : ℝ => t ^ 2) (by fun_prop)
      rw [if_pos rfl, heq, hev]; exact hvar
    · rw [if_neg hij]
      have hpair := (hindep.indepFun hij).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply i).aestronglyMeasurable
        (measurable_pi_apply j).aestronglyMeasurable
      rw [hpair, hEi i, hEi j, mul_zero]
  -- Second moment of the total: `∫ (∑ Xᵢ)² = m + 1`.
  have hSmemLp : MemLp (fun x : Fin (m + 1) → ℝ => ∑ i, x i) 2 (Measure.pi fun _ => P₁) :=
    memLp_finset_sum _ fun i _ => hL2i i
  have hSsq_int : Integrable (fun x : Fin (m + 1) → ℝ => (∑ i, x i) ^ 2)
      (Measure.pi fun _ => P₁) := by
    have := hSmemLp.integrable_mul hSmemLp
    simpa [Pi.mul_apply, pow_two] using this
  have hSsq : ∫ x : Fin (m + 1) → ℝ, (∑ i, x i) ^ 2 ∂(Measure.pi fun _ => P₁) = N := by
    have hexpand : (fun x : Fin (m + 1) → ℝ => (∑ i, x i) ^ 2)
        = fun x => ∑ i, ∑ j, x i * x j := by
      funext x; rw [pow_two, Fintype.sum_mul_sum]
    rw [hexpand, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint_ij i j]
    have hinner : ∀ i, ∫ x : Fin (m + 1) → ℝ, ∑ j, x i * x j ∂(Measure.pi fun _ => P₁) = 1 := by
      intro i
      rw [integral_finset_sum _ fun j _ => hint_ij i j]
      simp [hc i]
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hNdef]
    push_cast; ring
  -- Assemble: `∫ X̄² = (1/N²) · N = 1/N`.
  have hmean_sq_int : Integrable (fun x : Fin (m + 1) → ℝ => ((∑ i, x i) / N) ^ 2)
      (Measure.pi fun _ => P₁) := by
    have : (fun x : Fin (m + 1) → ℝ => ((∑ i, x i) / N) ^ 2)
        = fun x => (N ^ 2)⁻¹ * (∑ i, x i) ^ 2 := by
      funext x; rw [div_pow]; ring
    rw [this]; exact hSsq_int.const_mul _
  have hmeanRisk : ∫ x : Fin (m + 1) → ℝ, ((∑ i, x i) / N) ^ 2 ∂(Measure.pi fun _ => P₁)
      = 1 / N := by
    have hrw : (fun x : Fin (m + 1) → ℝ => ((∑ i, x i) / N) ^ 2)
        = fun x => (N ^ 2)⁻¹ * (∑ i, x i) ^ 2 := by funext x; rw [div_pow]; ring
    have hN0 : N ≠ 0 := hNpos.ne'
    rw [hrw, integral_const_mul, hSsq, pow_two, mul_inv, mul_assoc,
        inv_mul_cancel₀ hN0, mul_one, one_div]
  -- The `ℝ≥0∞`-risk is the `ENNReal.ofReal` of this Bochner integral.
  unfold locRisk
  rw [hf, ← ofReal_integral_eq_lintegral_ofReal hmean_sq_int
        (ae_of_all _ fun x => sq_nonneg _), hmeanRisk]

/-- **The normal law is least favourable for equivariant location estimation.** Over the
class of location families generated by an independent sample of centred unit-variance
observations, the risk of a minimum risk equivariant estimator is at most `1/n` — the
value it takes in the normal case (`locRisk_isLocMRE_gaussian_eq`). The minimum risk
equivariant risk is therefore maximized at the normal law.

The classical development notes, but does not prove, that for `n ≥ 3` the normal is the
only member of the class attaining `1/n`; that converse is not formalized. -/
theorem risk_le_gaussian_of_unitVariance (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (P₁ : Measure ℝ) [IsProbabilityMeasure P₁]
    -- USER-INPUT: the base member is an independent sample from `P₁`
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => P₁)
    -- USER-INPUT: the coordinates are centred with unit variance
    (hmean : ∫ t, t ∂P₁ = 0) (hvar : ∫ t, t ^ 2 ∂P₁ = 1)
    {δ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: `δ` is minimum risk equivariant under squared error
    (hMRE : IsLocMRE f (fun t : ℝ => t ^ 2) δ) :
    locRisk f (fun t : ℝ => t ^ 2) δ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  -- The sample mean is a measurable equivariant competitor with risk `1/(m+1)`
  -- (`locRisk_mean_eq_inv`); the minimum risk equivariant `δ` does at least as well.
  have hcomp := hMRE.2.2 (fun x => (∑ i, x i) / ((m : ℝ) + 1))
    measurable_sampleMean isLocEquivariant_sampleMean
  rwa [locRisk_mean_eq_inv f P₁ hf hmean hvar] at hcomp

/-- The bound of `risk_le_gaussian_of_unitVariance` is attained at the standard normal
law, where the sample mean is itself minimum risk equivariant. -/
theorem locRisk_isLocMRE_gaussian_eq (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    -- USER-INPUT: the base member is a standard normal independent sample
    (hf : locationBase f = Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)
    {δ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: `δ` is minimum risk equivariant under squared error
    (hMRE : IsLocMRE f (fun t : ℝ => t ^ 2) δ) :
    locRisk f (fun t : ℝ => t ^ 2) δ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  -- At the standard normal the sample mean is itself minimum risk equivariant
  -- (`isLocMRE_mean_gaussian`); two minimum risk equivariant estimators have equal risk,
  -- and that common value is `1/(m+1)` (`locRisk_mean_eq_inv`).
  have hXbar := isLocMRE_mean_gaussian f (v := 1) one_ne_zero hf
  have hle1 : locRisk f (fun t : ℝ => t ^ 2) δ
      ≤ locRisk f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1)) :=
    hMRE.2.2 _ hXbar.1 hXbar.2.1
  have hle2 : locRisk f (fun t : ℝ => t ^ 2) (fun x => (∑ i, x i) / ((m : ℝ) + 1))
      ≤ locRisk f (fun t : ℝ => t ^ 2) δ :=
    hXbar.2.2 _ hMRE.1 hMRE.2.1
  have hmean : ∫ t, t ∂(ProbabilityTheory.gaussianReal 0 1) = 0 :=
    ProbabilityTheory.integral_id_gaussianReal
  have hvar : ∫ t, t ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
    have hV := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1)
    rw [ProbabilityTheory.variance_eq_integral aemeasurable_id] at hV
    simpa [ProbabilityTheory.integral_id_gaussianReal] using hV
  rw [le_antisymm hle1 hle2, locRisk_mean_eq_inv f _ hf hmean hvar]

end LocationExamples

end StatLean.PointEstimation
