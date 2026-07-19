import StatLean.PointEstimation.Equivariance.LocationMRE
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

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
  unfold pitmanEstimator
  have hjoint : Measurable fun p : (Fin n → ℝ) × ℝ => f (p.1 - p.2 • (1 : Fin n → ℝ)) :=
    hf.comp (measurable_fst.sub (measurable_snd.smul_const (1 : Fin n → ℝ)))
  have hN : Measurable fun x => ∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ)) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (measurable_snd.mul hjoint).stronglyMeasurable).measurable
  have hD : Measurable fun x => ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right'
      hjoint.stronglyMeasurable).measurable
  exact hN.div hD

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
  intro a x
  have hDshift : (∫ u : ℝ, f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
      = ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) := by
    have hpt : (fun u : ℝ => f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
        = fun u : ℝ => f (x - (u - a) • (1 : Fin n → ℝ)) := by
      funext u
      congr 1
      rw [sub_smul]; abel
    rw [hpt]
    exact integral_sub_right_eq_self (fun v : ℝ => f (x - v • (1 : Fin n → ℝ))) a
  have hNshift : (∫ u : ℝ, u * f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
      = (∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ)))
        + a * ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) := by
    have hHint : Integrable (fun u : ℝ => (u - a) * f (x - (u - a) • (1 : Fin n → ℝ))) :=
      Integrable.comp_sub_right (hnum x) a
    have hgint : Integrable (fun u : ℝ => f (x - (u - a) • (1 : Fin n → ℝ))) :=
      Integrable.comp_sub_right (hden x) a
    have hpt : (fun u : ℝ => u * f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
        = fun u : ℝ => (u - a) * f (x - (u - a) • (1 : Fin n → ℝ))
          + a * f (x - (u - a) • (1 : Fin n → ℝ)) := by
      funext u
      have hvec : x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)
          = x - (u - a) • (1 : Fin n → ℝ) := by rw [sub_smul]; abel
      rw [hvec]; ring
    have e1 : (∫ u : ℝ, (u - a) * f (x - (u - a) • (1 : Fin n → ℝ)))
        = ∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ)) :=
      integral_sub_right_eq_self (fun v : ℝ => v * f (x - v • (1 : Fin n → ℝ))) a
    have e2 : (∫ u : ℝ, f (x - (u - a) • (1 : Fin n → ℝ)))
        = ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) :=
      integral_sub_right_eq_self (fun v : ℝ => f (x - v • (1 : Fin n → ℝ))) a
    rw [hpt, integral_add hHint (Integrable.const_mul hgint a), integral_const_mul, e1, e2]
  show pitmanEstimator f (x + a • (1 : Fin n → ℝ)) = pitmanEstimator f x + a
  unfold pitmanEstimator
  rw [hNshift, hDshift, add_div, mul_div_assoc, div_self (hden0 x), mul_one]

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
  -- Contract-level debt (reported). This is the substantive change of variables. The
  -- intended route identifies the conditional law of the data given `diffs` as the
  -- normalized slice of the joint density via `ForMathlib.CondDistribDensity`
  -- (`condDistrib_withDensity_prod_ae_eq`) — **which is itself a statement-first stub with
  -- `sorry` in this tree**, not a closed lemma — and then applies the unit-Jacobian shear
  -- `y_i = x_i - x_n`, `y_n = x_n` to turn the slice integral into the displayed ratio of
  -- one-dimensional integrals. Blocked upstream; no axiom-clean proof is available here.
  sorry

/-- Conditional integrability of the reference estimator `δ₀ x = x n` against the fibre
kernel of the differences, in *every* fibre — the hypothesis `isLocMRE_sq_of_condMean`
consumes. Named debt (the one lifted `private` sorry of this file): it is not implied by
the pointwise convergence of the Pitman integrals `hnum`/`hden`, and establishing it
requires the same conditional-law-as-normalized-slice identification
(`ForMathlib.CondDistribDensity`, itself a `sorry` stub) plus the unit-Jacobian shear used
in `pitmanEstimator_eq_sub_condMean`. -/
private lemma integrable_lastCoord_orbitCondKernel (f : (Fin (m + 1) → ℝ) → ℝ)
    [IsProbabilityMeasure (locationBase f)] (y : Fin m → ℝ) :
    Integrable (fun x => x (Fin.last m)) (orbitCondKernel (locationBase f) diffs y) := by
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
  -- The closed form equals the squared-error conditional-mean MRE estimator with reference
  -- `δ₀ x = x n` (`pitmanEstimator_eq_sub_condMean`), which is MRE by `isLocMRE_sq_of_condMean`.
  have heq₀ : IsLocEquivariant (fun x : Fin (m + 1) → ℝ => x (Fin.last m)) := by
    intro a x
    show (x + a • (1 : Fin (m + 1) → ℝ)) (Fin.last m) = x (Fin.last m) + a
    simp [Pi.add_apply, Pi.smul_apply, Pi.one_apply]
  have heqform : pitmanEstimator f = fun x => x (Fin.last m) -
      ∫ z, z (Fin.last m) ∂(orbitCondKernel (locationBase f) diffs (diffs x)) :=
    funext (pitmanEstimator_eq_sub_condMean f hf hfnn hnum hden hden0)
  rw [heqform]
  exact isLocMRE_sq_of_condMean f (measurable_pi_apply (Fin.last m)) heq₀ hfin
    (integrable_lastCoord_orbitCondKernel f)

end Pitman

end StatLean.PointEstimation
