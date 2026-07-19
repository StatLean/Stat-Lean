import StatLean.PointEstimation.Equivariance.LocationMRE
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
  -- Contract-level debt (reported). Intended route: `X̄` is location equivariant and
  -- `X̄ − X n` is a function of `diffs`, so by Basu's theorem
  -- (`Completeness.Basu.indepFun_of_boundedlyComplete_sufficient`) the complete sufficient
  -- statistic `X̄` is independent of the ancillary `diffs`; hence the conditional mean
  -- `E₀[X n | diffs]` is a.e. constant and the Pitman estimator collapses to `X̄`, which is
  -- then MRE by `pitmanEstimator_isLocMRE`. That route runs through `Pitman` and the
  -- `ForMathlib.CondDistribDensity` stub (a `sorry` in this tree), so no axiom-clean proof
  -- is available here. The Kagan–Linnik–Rao converse is out of scope (see the docstring).
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
  -- Named debt: the second-moment computation `E₀[X̄²] = 1/(m+1)`. Under the iid law
  -- `hf`, expand `(∑ Xᵢ)²/(m+1)²` and integrate: the `m+1` diagonal terms contribute
  -- `∫t² = 1` each (`hvar`) and the off-diagonal terms vanish by independence and
  -- `∫t = 0` (`hmean`), giving `(m+1)/(m+1)² = 1/(m+1)`. The `∫⁻ ofReal`/`ofReal ∫`
  -- bridge uses square-integrability from `hvar`. Left as a (mechanical but lengthy)
  -- moment-calculus debt; nothing false here.
  sorry

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
