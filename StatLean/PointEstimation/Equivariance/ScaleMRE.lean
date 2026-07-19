import StatLean.PointEstimation.Equivariance.ConditionalRiskEngine
import StatLean.PointEstimation.Equivariance.ScaleStructure
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The minimum risk equivariant scale estimator

The scale counterpart of `LocationMRE`. The scale-equivariant class is `δ₀ / w ∘ scaleZ`
(`ScaleStructure`), so minimizing the risk over it reduces to a fibrewise minimization of
the conditional expected loss `E₁{γ[δ₀(X)/w] | z}` given the maximal invariant — the same
engine as in the location case with the template `F w x = δ₀ x / w` in place of
`F w x = δ₀ x − w`.

* `isScaleMRE_of_conditional_min` — the construction;
* `exists_isScaleMRE_of_convex` — existence when `v ↦ γ(eᵛ)` is convex and not monotone,
  the multiplicative form of the convexity condition;
* `isScaleMRE_steinLoss` — the explicit minimum risk equivariant estimator of `τ^r` under
  Stein's loss `γ(v) = v − log v − 1`, namely `δ₀(X) / E₁[δ₀(X) | z]`;
* `isScaleMRE_standardizedSquared` — the companion explicit form under the standardized
  squared-error loss `γ(v) = (v − 1)²`, a ratio of conditional moments
  `δ₀(X)·E₁[δ₀(X)|z] / E₁[δ₀²(X)|z]`.

**Reference.** Classical scale-equivariant estimation; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* The multiplicative group acts transitively on the scale parameter, so the risk of a
  scale-equivariant estimator is constant and minimizing it is well posed; this is the
  general constant-risk result specialised, not a separate fact.
* Because `scaleZ` uses division, Lean's `x / 0 = 0` convention makes `scaleZ` invariant
  under positive scaling **everywhere**, including on `{xₙ = 0}`. The constructed
  estimators are therefore equivariant without any restriction. The null-set hypothesis
  `hnull` is needed for the *minimality* half instead: comparing against an arbitrary
  equivariant competitor uses the representation `δ = δ₀ / w ∘ scaleZ`, which is only
  available off `{xₙ = 0}`. The classical development records this as "z is defined when
  `xₙ ≠ 0`, hence with probability one".
* The convexity condition is stated on the logarithmic reparametrization `v ↦ γ(eᵛ)`,
  which is what turns the multiplicative fibrewise minimization into the additive one
  solved in the location case; the accompanying positivity of the reference estimator is
  the "without loss of generality `δ ≥ 0`" of the classical argument, made explicit.
* Stein's loss is stated with the conditional mean, matching the classical form. The
  classical statement asserts *uniqueness* of the minimizer; only optimality is
  formalized here.
* The standardized squared-error form is the companion of the same conditional
  minimization for the loss `(d − τ^r)²/τ^{2r}`, whose solution is the ratio of the first
  and second conditional moments of the reference estimator. Comparing the two makes the
  classical point that Stein's loss yields the larger estimator, since the second
  conditional moment dominates the square of the first.
* As in the location case, `hmin` uses `∀ᵐ` where the classical hypothesis is stated for
  every fibre, and measurability of the fibrewise minimizer is a Lean-side requirement
  with no classical counterpart.

**Bibliographic comments.** Equivariant estimation of a scale parameter is due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421. The entropy loss used
here was introduced by W. James and C. Stein, "Estimation with quadratic loss," *Proc.
Fourth Berkeley Symp. Math. Statist. Probab.*, vol. 1, Univ. California Press, 1961,
361–379; for the admissibility questions in the background see C. Stein, "The
admissibility of Pitman's estimator of a single location parameter," *Ann. Math. Statist.*
**30** (1959), 970–979.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section ScaleMRE

variable {m : ℕ}

/-- **Stein's (entropy) loss** for a scale parameter in standardized form,
`γ(v) = v − log v − 1`, so that `L(τ, d) = d/τ^r − log(d/τ^r) − 1`.

Unlike the standardized squared-error loss it penalises overestimation and
underestimation comparably: it tends to infinity at both `0` and `∞`. Edge behaviour:
`Real.log` is `0` at `0` and reads the absolute value on negatives, so `steinLoss` is
junk for non-positive arguments; every statement below constrains the estimator to be
positive. -/
noncomputable def steinLoss (v : ℝ) : ℝ := v - Real.log v - 1

/-- **The minimum risk equivariant scale estimator.** Let `δ₀` be a measurable
scale-equivariant estimator of `τ^r` with finite risk, nowhere zero, and let `w*` be a
measurable positive function of the maximal invariant which, in almost every fibre,
minimizes the conditional expected loss `E₁{γ[δ₀(X)/w] | z}` over positive constants `w`.
Then `δ₀ / w* ∘ scaleZ` is minimum risk equivariant. -/
theorem isScaleMRE_of_conditional_min (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member (at `τ = 1`) is a probability law
    [IsProbabilityMeasure P₀]
    (γ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed for the disintegration
    (hγ : Measurable γ)
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator, the caller's free choice
    (heq₀ : IsScaleEquivariant r δ₀)
    -- LEAN-ONLY: it never vanishes, so the representation of the equivariant class is
    -- available (see `ScaleStructure`)
    (h₀ne : ∀ x, δ₀ x ≠ 0)
    -- USER-INPUT: it has finite risk, so the conditional minimization is meaningful
    (hfin : scaleRisk P₀ γ δ₀ ≠ ∞)
    -- USER-INPUT: the last coordinate vanishes with probability zero, so the maximal
    -- invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    {wStar : (Fin m → ℝ) × ℝ → ℝ}
    -- USER-INPUT: the fibrewise minimizer, supplied measurably and positively
    (hwStar : Measurable wStar) (hwpos : ∀ z, 0 < wStar z)
    -- USER-INPUT: `w*` minimizes the conditional expected loss in almost every fibre
    (hmin : ∀ᵐ z ∂(P₀.map scaleZ), ∀ w : ℝ, 0 < w →
      ∫⁻ x, ENNReal.ofReal (γ (δ₀ x / wStar z)) ∂(orbitCondKernel P₀ scaleZ z) ≤
        ∫⁻ x, ENNReal.ofReal (γ (δ₀ x / w)) ∂(orbitCondKernel P₀ scaleZ z)) :
    IsScaleMRE P₀ γ r (fun x => δ₀ x / wStar (scaleZ x)) := by
  sorry

/-- **Existence of a minimum risk equivariant scale estimator for a logarithmically
convex, non-monotone loss.** Reparametrising `w = eᵛ` turns the multiplicative fibrewise
minimization into the additive one of the location case, so the same convexity and
non-monotonicity conditions apply — now to `v ↦ γ(eᵛ)`. Uniqueness under strict convexity
is not formalized. -/
theorem exists_isScaleMRE_of_convex (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member is a probability law
    [IsProbabilityMeasure P₀]
    (γ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss
    (hγ : Measurable γ)
    -- USER-INPUT: the loss is convex in the logarithmic parametrization
    (hconv : ConvexOn ℝ Set.univ fun v => γ (Real.exp v))
    -- USER-INPUT: and not monotone there, so the fibrewise minimum is attained
    (hnotmono : (¬ Monotone fun v => γ (Real.exp v)) ∧ ¬ Antitone fun v => γ (Real.exp v))
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator with finite risk
    (heq₀ : IsScaleEquivariant r δ₀)
    (hfin : scaleRisk P₀ γ δ₀ ≠ ∞)
    -- USER-INPUT: taking only positive values; this is the classical "without loss of
    -- generality the estimator is nonnegative", made explicit
    (h₀pos : ∀ x, 0 < δ₀ x)
    -- USER-INPUT: the maximal invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0) :
    ∃ δ, IsScaleMRE P₀ γ r δ := by
  sorry

/-- **The minimum risk equivariant estimator of `τ^r` under Stein's loss** is the
reference equivariant estimator divided by its conditional mean given the maximal
invariant: `δ*(X) = δ₀(X) / E₁[δ₀(X) | z]`.

The classical statement adds that the minimizer is unique; only optimality is formalized
here. -/
theorem isScaleMRE_steinLoss (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member is a probability law
    [IsProbabilityMeasure P₀]
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator taking positive values
    (heq₀ : IsScaleEquivariant r δ₀) (h₀pos : ∀ x, 0 < δ₀ x)
    -- USER-INPUT: it has finite risk under Stein's loss
    (hfin : scaleRisk P₀ steinLoss δ₀ ≠ ∞)
    -- USER-INPUT: the maximal invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    -- USER-INPUT: the conditional mean exists in every fibre
    (hint : ∀ z, Integrable δ₀ (orbitCondKernel P₀ scaleZ z))
    -- USER-INPUT: and is positive, so dividing by it is legitimate
    (hcondpos : ∀ z, 0 < ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ z)) :
    IsScaleMRE P₀ steinLoss r
      (fun x => δ₀ x / ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) := by
  sorry

/-- **The minimum risk equivariant estimator of `τ^r` under the standardized
squared-error loss** `γ(v) = (v − 1)²`, i.e. `L(τ, d) = (d − τ^r)²/τ^{2r}`: the ratio of
conditional moments `δ*(X) = δ₀(X)·E₁[δ₀(X)|z] / E₁[δ₀²(X)|z]`.

Comparing with `isScaleMRE_steinLoss` recovers the classical observation that Stein's
loss produces the larger estimator, since the second conditional moment always dominates
the square of the first. -/
theorem isScaleMRE_standardizedSquared (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member is a probability law
    [IsProbabilityMeasure P₀]
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator taking positive values
    (heq₀ : IsScaleEquivariant r δ₀) (h₀pos : ∀ x, 0 < δ₀ x)
    -- USER-INPUT: it has finite risk under the standardized squared-error loss
    (hfin : scaleRisk P₀ (fun v : ℝ => (v - 1) ^ 2) δ₀ ≠ ∞)
    -- USER-INPUT: the maximal invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    -- USER-INPUT: the first two conditional moments exist in every fibre
    (hint₁ : ∀ z, Integrable δ₀ (orbitCondKernel P₀ scaleZ z))
    (hint₂ : ∀ z, Integrable (fun y => δ₀ y ^ 2) (orbitCondKernel P₀ scaleZ z))
    -- USER-INPUT: the second conditional moment is positive, so the ratio is not junk
    (hpos₂ : ∀ z, 0 < ∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ z)) :
    IsScaleMRE P₀ (fun v : ℝ => (v - 1) ^ 2) r
      (fun x => δ₀ x * (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) /
        (∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ x)))) := by
  sorry

end ScaleMRE

end StatLean.PointEstimation
