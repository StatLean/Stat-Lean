import StatLean.PointEstimation.UMVU.Defs

/-!
# Unbiased estimation: the affine structure of the unbiased class, and uniqueness of UMVU

Two structural facts underlying the whole theory of minimum-variance unbiased estimation.

* `isUnbiased_iff_sub_unbiasedZero` — once one unbiased estimator `δ₀` of `g` is available,
  the unbiased estimators of `g` are exactly the differences `δ₀ - U` with `U` an unbiased
  estimator of zero. Estimating `g` well is therefore the same problem as approximating `δ₀`
  from the linear space of unbiased estimators of zero, which is what makes the covariance
  criterion (and its projection reading) possible.
* `isUMVU_unique` — a uniformly minimum variance unbiased estimator is unique up to almost
  everywhere equality under every member of the model. This is why one speaks of *the* UMVU
  estimator.

**Reference.** Classical unbiased-estimation theory: the parametrization of the unbiased class
and the uniqueness of the minimum-variance element.

**Proof formalization notes.**
* The equivalence is stated in the "difference" form `IsUnbiasedZero P (δ₀ - δ)` rather than
  as an existential `∃ U, δ = δ₀ - U`: the two are trivially interchangeable (take
  `U := δ₀ - δ`), and the difference form is the one every downstream argument uses. The set
  form of the classical statement follows immediately and is not stated separately.
* Integrability of `δ₀` and of `δ` under every member is required in both directions: means
  split additively only for integrable functions, and unbiasedness as defined is an equation
  between Bochner integrals, whose junk value `0` for non-integrable functions would
  otherwise make the equivalence false rather than merely unprovable.
* Uniqueness is proved parameter by parameter and needs only local minimality at that
  parameter: given two UMVU estimators, their variances agree, the average
  `(δ₁ + δ₂)/2` is again unbiased and square-integrable, and comparing its variance with the
  common value forces equality in the Cauchy–Schwarz bound for `cov(δ₁, δ₂)`, hence an affine
  relation between the centered estimators; equal variances and equal means then give
  `δ₁ = δ₂` almost everywhere. The degenerate case of zero variance is the statement that both
  are almost everywhere constant, equal to `g θ`.
* No measurability hypothesis appears: `MemEstL2` already carries almost-everywhere strong
  measurability under each member through `MemLp`.

**Bibliographic comments.** The systematic theory of minimum-variance unbiased estimation is
due to C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91; "Sufficient statistics and
minimum variance estimates," *Proc. Camb. Phil. Soc.* **45** (1949), 213–218), D. Blackwell
("Conditional expectation and unbiased sequential estimation," *Ann. Math. Statist.* **18**
(1947), 105–110) and E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and
unbiased estimation," *Sankhyā* **10** (1950), 305–340). The reading of the unbiased class as
an affine subspace, with the minimum-variance element obtained by projecting onto the space of
unbiased estimators of zero, is developed by R. R. Bahadur ("On unbiased estimates of
uniformly minimum variance," *Sankhyā* **18** (1957), 211–224).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **The unbiased class is `δ₀` minus the unbiased estimators of zero.** Given one unbiased
estimator `δ₀` of `g`, an integrable `δ` is unbiased for `g` exactly when `δ₀ - δ` is an
unbiased estimator of zero. -/
theorem isUnbiased_iff_sub_unbiasedZero (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {δ₀ δ : 𝓧 → ℝ}
    -- USER-INPUT: a reference unbiased estimator of the estimand; the classical starting point
    (hδ₀ : IsUnbiased P g δ₀)
    -- LEAN-ONLY: integrability of the reference estimator under every member, so that means
    -- split additively (Bochner integrals return junk `0` otherwise)
    (hδ₀i : ∀ θ, Integrable δ₀ (P θ))
    -- LEAN-ONLY: integrability of the candidate estimator, same reason
    (hδi : ∀ θ, Integrable δ (P θ)) :
    IsUnbiased P g δ ↔ IsUnbiasedZero P (fun x => δ₀ x - δ x) := by
  sorry

/-- **Uniqueness of the UMVU estimator.** Two uniformly minimum variance unbiased estimators
of the same estimand agree almost everywhere under every member of the model. -/
theorem isUMVU_unique (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ)
    {δ₁ δ₂ : 𝓧 → ℝ}
    -- USER-INPUT: the first UMVU estimator
    (h₁ : IsUMVU P g δ₁)
    -- USER-INPUT: the second UMVU estimator of the same estimand
    (h₂ : IsUMVU P g δ₂) (θ : Θ) :
    δ₁ =ᵐ[P θ] δ₂ := by
  sorry

end StatLean.PointEstimation
