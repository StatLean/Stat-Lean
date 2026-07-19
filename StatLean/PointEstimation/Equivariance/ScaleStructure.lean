import StatLean.PointEstimation.Equivariance.Defs
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Scale and location-scale equivariance — the structure of the equivariant class

The scale model: data `X` with joint density `τ^{-n} f(x/τ)`, estimand `τ^r`, loss
`γ(d/τ^r)`. Multiplication by a positive constant acts transitively on the parameter
space, so the risk of a scale-equivariant estimator is constant and a minimum risk
equivariant estimator is a reasonable target. This file supplies the structural half of
the theory — the description of the equivariant class — mirroring `LocationStructure`,
with division replacing subtraction and the coordinate ratios replacing the differences.

* `IsScaleInvariant`, `isScaleEquivariant_iff_div_invariant` — an estimator is scale
  equivariant iff it is a fixed scale-equivariant `δ₀` divided by a scale-invariant
  function;
* `isScaleInvariant_iff_factors_scaleZ` — a scale-invariant function is exactly a
  function of the maximal invariant `scaleZ` (coordinate ratios plus the sign of the last
  coordinate), off the null set where the last coordinate vanishes;
* `isScaleEquivariant_iff_div_scaleZ` — the two combined: `δ = δ₀ / w ∘ scaleZ`;
* `IsLocScaleEquivariantLocation`, `IsLocScaleEquivariantScale` and
  `isLocScaleEquivariant_iff_exists_scaleZ_diffs_rep` — the location-scale analogue,
  where the location-equivariant estimators are `δ₀ − w(z)·δ₁` with `δ₁` a positive
  scale-equivariant estimator and `z` the maximal invariant of the differences.

**Reference.** Classical scale- and location-scale-equivariant estimation; original
sources in the bibliographic comments below.

**Proof formalization notes.**
* `scaleZ` is defined only meaningfully off `{xₙ = 0}`, a null set for any of the models
  considered. The classical statement records this in a parenthesis; here the
  factorization statements are **explicitly restricted** to `{xₙ ≠ 0}` on *both* sides of
  the equivalence. Restricting only the right-hand side would make the equivalence false,
  since a function agreeing with `w ∘ scaleZ` off a set says nothing about its behaviour
  on that set.
* The reference estimator `δ₀` is assumed nowhere zero. The classical development divides
  by it without comment; in Lean, `x / 0 = 0` would silently break the reconstruction
  `u = δ₀ / δ`, so the hypothesis is made explicit. Because the estimand is `τ^r > 0`,
  this costs nothing statistically.
* The measurable version of the factorization is built from the explicit section
  `(z, s) ↦ Fin.snoc (fun i => z i * s) s` of `scaleZ`, which is measurable and inverts
  `scaleZ` on its range; this is what the conditional-minimization argument consumes.
* In the location-scale statement the maximal invariant is `scaleZ ∘ diffs`: first reduce
  by translations to the differences, then by scalings to their ratios. The index
  bookkeeping is `n = m + 2` observations, `m + 1` differences, `m` ratios plus a sign.

**Bibliographic comments.** Equivariant estimation of scale and location-scale parameters
is due to E. J. G. Pitman, "The estimation of the location and scale parameters of a
continuous population of any given form," *Biometrika* **30** (1939), 391–421. The
general group-theoretic formulation is due to G. A. Hunt and C. Stein (unpublished
manuscript, 1946), first reported in print by M. A. Girshick and L. J. Savage, "Bayes and
minimax estimates for quadratic loss functions," *Proc. Second Berkeley Symp. Math.
Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Scale

variable {m n : ℕ}

/-! ### Definitions -/

/-- **Scale-invariant function** of the data: `u(bx) = u(x)` for every `b > 0`. This is
the scale analogue of translation invariance; its maximal invariant is `scaleZ`. Values
at `b ≤ 0` are unconstrained, matching the fact that the acting group is the positive
multiplicative reals. -/
def IsScaleInvariant (u : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, u (b • x) = u x

/-- **Location-scale equivariant estimator of the location parameter**: under the
transformations `x ↦ a𝟙 + bx` (`b > 0`) of the sample space, which send `(ξ, τ)` to
`(a + bξ, bτ)`, an estimator of `ξ` must satisfy `δ(a𝟙 + bx) = a + bδ(x)`. -/
def IsLocScaleEquivariantLocation (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (a : ℝ) ⦃b : ℝ⦄, 0 < b → ∀ x, δ (a • (1 : Fin n → ℝ) + b • x) = a + b * δ x

/-- **Location-scale equivariant estimator of the scale parameter**: under the same
transformations, an estimator of `τ` must satisfy `δ(a𝟙 + bx) = bδ(x)` — unchanged by the
location shift and homogeneous of degree one in the scale. -/
def IsLocScaleEquivariantScale (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (a : ℝ) ⦃b : ℝ⦄, 0 < b → ∀ x, δ (a • (1 : Fin n → ℝ) + b • x) = b * δ x

/-! ### Elementary closure properties -/

/-- The scale-invariant statistic is measurable. -/
theorem measurable_scaleZ :
    Measurable (scaleZ : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ) := by
  sorry

/-- Dividing a scale-equivariant estimator by a scale-invariant function leaves it scale
equivariant. -/
theorem IsScaleEquivariant.div_invariant {r : ℕ} {δ : (Fin n → ℝ) → ℝ}
    {u : (Fin n → ℝ) → ℝ} (hδ : IsScaleEquivariant r δ) (hu : IsScaleInvariant u) :
    IsScaleEquivariant r fun x => δ x / u x := by
  sorry

/-! ### Structure of the scale-equivariant class -/

/-- **An estimator is scale equivariant iff it is a fixed scale-equivariant estimator
divided by a scale-invariant function.** The scale analogue of the additive
decomposition of the location-equivariant class. -/
theorem isScaleEquivariant_iff_div_invariant {r : ℕ} {δ₀ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: a reference scale-equivariant estimator, the caller's free choice
    (h₀ : IsScaleEquivariant r δ₀)
    -- LEAN-ONLY: the reference estimator never vanishes; the classical argument divides
    -- by it silently, and `x / 0 = 0` would break the reconstruction. Harmless, since
    -- the estimand is positive
    (h₀ne : ∀ x, δ₀ x ≠ 0)
    (δ : (Fin n → ℝ) → ℝ) :
    IsScaleEquivariant r δ ↔ ∃ u, IsScaleInvariant u ∧ ∀ x, δ x = δ₀ x / u x := by
  sorry

/-- **A function is scale-invariant iff it factors through the maximal invariant**
`scaleZ`, off the null set where the last coordinate vanishes. Both sides of the
equivalence are restricted to that set, since the behaviour of the function on it is not
determined either way. -/
theorem isScaleInvariant_iff_factors_scaleZ (u : (Fin (m + 1) → ℝ) → ℝ) :
    (∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → u (b • x) = u x) ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ, ∀ x, x (Fin.last m) ≠ 0 → u x = w (scaleZ x) := by
  sorry

/-- Measurable version of the factorization through `scaleZ`, as consumed by the
conditional-minimization argument. -/
theorem isScaleInvariant_iff_factors_scaleZ_measurable (u : (Fin (m + 1) → ℝ) → ℝ) :
    (Measurable u ∧
        ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → u (b • x) = u x) ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ, Measurable w ∧
        ∀ x, x (Fin.last m) ≠ 0 → u x = w (scaleZ x) := by
  sorry

/-- **Representation of the scale-equivariant class.** Relative to a nowhere-vanishing
reference scale-equivariant estimator `δ₀`, the scale-equivariant estimators are exactly
`δ₀ / w ∘ scaleZ` as `w` ranges over functions of the maximal invariant — off the null
set where the last coordinate vanishes. -/
theorem isScaleEquivariant_iff_div_scaleZ {r : ℕ} {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: a reference scale-equivariant estimator, the caller's free choice
    (h₀ : IsScaleEquivariant r δ₀)
    -- LEAN-ONLY: the reference estimator never vanishes (see above)
    (h₀ne : ∀ x, δ₀ x ≠ 0)
    (δ : (Fin (m + 1) → ℝ) → ℝ) :
    (∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → δ (b • x) = b ^ r * δ x) ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ,
        ∀ x, x (Fin.last m) ≠ 0 → δ x = δ₀ x / w (scaleZ x) := by
  sorry

/-! ### Location-scale families -/

/-- **Representation of the location-scale equivariant class for the location
parameter.** Given a reference estimator `δ₀` of the location parameter and a
strictly positive reference estimator `δ₁` of the scale parameter, both equivariant under
the location-scale group, an estimator `δ` is location-scale equivariant for the location
parameter iff `δ = δ₀ − w(z)·δ₁` for a function `w` of the maximal invariant
`z = scaleZ (diffs x)`: reduce by translations to the differences, then by scalings to
their ratios. -/
theorem isLocScaleEquivariant_iff_exists_scaleZ_diffs_rep
    {δ₀ δ₁ : (Fin (m + 2) → ℝ) → ℝ}
    -- USER-INPUT: a reference location-scale equivariant estimator of the location
    (h₀ : IsLocScaleEquivariantLocation δ₀)
    -- USER-INPUT: a reference location-scale equivariant estimator of the scale
    (h₁ : IsLocScaleEquivariantScale δ₁)
    -- USER-INPUT: the scale estimator takes only positive values, so dividing by it is
    -- legitimate; the classical statement makes the same requirement
    (h₁pos : ∀ x, 0 < δ₁ x)
    (δ : (Fin (m + 2) → ℝ) → ℝ) :
    IsLocScaleEquivariantLocation δ ↔
      ∃ w : (Fin m → ℝ) × ℝ → ℝ, ∀ x, diffs x (Fin.last m) ≠ 0 →
        δ x = δ₀ x - w (scaleZ (diffs x)) * δ₁ x := by
  sorry

end Scale

end StatLean.PointEstimation
