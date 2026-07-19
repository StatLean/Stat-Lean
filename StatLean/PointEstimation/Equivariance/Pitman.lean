import StatLean.PointEstimation.Equivariance.LocationMRE

/-!
# The Pitman estimator of location

Under squared error the minimum risk equivariant location estimator subtracts the
conditional mean of a reference equivariant estimator given the differences. Taking the
last coordinate as the reference estimator and carrying out the change of variables
`yᵢ = xᵢ − xₙ`, `yₙ = xₙ` (of unit Jacobian) turns that conditional mean into an explicit
ratio of one-dimensional integrals against the density:

`δ*(x) = (∫ u · f(x₁ − u, …, xₙ − u) du) / (∫ f(x₁ − u, …, xₙ − u) du)`.

This is `pitmanEstimator`, fixed in the data model of this area. The file proves it is
equivariant, that it coincides with the conditional-mean form, and that it is minimum
risk equivariant.

**Reference.** Classical location-equivariant estimation; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* Equivariance is the substitution `u ↦ u + a` in both integrals: the denominator is
  translation-invariant and the numerator picks up `a` times the denominator. Splitting
  the numerator requires the two integrands to be integrable, and dividing requires the
  denominator to be nonzero; these are the side conditions attached to every statement
  below. The classical development leaves them implicit.
* `pitmanEstimator_eq_sub_condMean` isolates the substantive step — the identification of
  the closed form with `xₙ − E₀[Xₙ | Y]` — as a named lemma rather than burying it inside
  the main theorem, since it is the change of variables that carries all the content.
* Measurability of the closed form is not assumed: it is derived (as
  `measurable_pitmanEstimator`) from measurability of the density, since assuming it
  would hide a genuine obligation behind a hypothesis.
* The finite-risk hypothesis is stated for the concrete reference estimator (the last
  coordinate) that the derivation uses, rather than as an abstract "some equivariant
  estimator has finite risk".
* Edge behaviour: `pitmanEstimator` divides two Bochner integrals, so it returns the junk
  value `0` wherever the denominator vanishes; `hden0` excludes that on the statements
  that need it.

**Bibliographic comments.** The estimator and its derivation are due to E. J. G. Pitman,
"The estimation of the location and scale parameters of a continuous population of any
given form," *Biometrika* **30** (1939), 391–421. Its admissibility for a single location
parameter was proved by C. Stein, "The admissibility of Pitman's estimator of a single
location parameter," *Ann. Math. Statist.* **30** (1959), 970–979.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Pitman

variable {m n : ℕ}

/-- The closed form is measurable whenever the density is and the defining integrals
converge. -/
theorem measurable_pitmanEstimator (f : (Fin n → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of the density; drives joint measurability of the
    -- integrands and hence measurability of the two integrals
    (hf : Measurable f)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin n → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin n → ℝ))) :
    Measurable (pitmanEstimator f) := by
  sorry

/-- **The Pitman estimator is location equivariant.** Substituting `u ↦ u + a` leaves the
denominator unchanged and adds `a` times the denominator to the numerator. -/
theorem pitmanEstimator_isLocEquivariant (f : (Fin n → ℝ) → ℝ)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin n → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin n → ℝ)))
    -- USER-INPUT: the denominator does not vanish, so the ratio is not junk
    (hden0 : ∀ x, (∫ u : ℝ, f (x - u • (1 : Fin n → ℝ))) ≠ 0) :
    IsLocEquivariant (pitmanEstimator f) := by
  sorry

/-- **The closed form is the conditional-mean form.** Taking the last coordinate as
reference equivariant estimator, the change of variables `yᵢ = xᵢ − xₙ`, `yₙ = xₙ` has
unit Jacobian and identifies the ratio of integrals with `xₙ − E₀[Xₙ | Y]`. -/
theorem pitmanEstimator_eq_sub_condMean (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    -- LEAN-ONLY: measurability of the density
    (hf : Measurable f)
    -- USER-INPUT: the density is nonnegative, so it is the density of `locationBase f`
    (hfnn : ∀ x, 0 ≤ f x)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator does not vanish
    (hden0 : ∀ x, (∫ u : ℝ, f (x - u • (1 : Fin (m + 1) → ℝ))) ≠ 0)
    (x : Fin (m + 1) → ℝ) :
    pitmanEstimator f x = x (Fin.last m) -
      ∫ z, z (Fin.last m)
        ∂(orbitCondKernel (locationBase f) diffs (diffs x)) := by
  sorry

/-- **The Pitman estimator is the minimum risk equivariant estimator of location under
squared error.** -/
theorem pitmanEstimator_isLocMRE (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    -- LEAN-ONLY: measurability of the density
    (hf : Measurable f)
    -- USER-INPUT: the density is nonnegative
    (hfnn : ∀ x, 0 ≤ f x)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator does not vanish
    (hden0 : ∀ x, (∫ u : ℝ, f (x - u • (1 : Fin (m + 1) → ℝ))) ≠ 0)
    -- USER-INPUT: the reference equivariant estimator (the last coordinate) has finite
    -- risk, which is what makes the conditional minimization meaningful
    (hfin : locRisk f (fun t : ℝ => t ^ 2) (fun x => x (Fin.last m)) ≠ ∞) :
    IsLocMRE f (fun t : ℝ => t ^ 2) (pitmanEstimator f) := by
  sorry

end Pitman

end StatLean.PointEstimation
