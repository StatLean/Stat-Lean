import StatLean.PointEstimation.Equivariance.Defs
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Location equivariance — constant risk and the structure of the equivariant class

The concrete location model on `Fin (m+1) → ℝ`: data `X` with joint density `f(x − ξ𝟙)`,
loss `ρ(d − ξ)`. This file establishes the two facts that reduce minimum risk equivariant
estimation to an ordinary minimization problem.

* **Constant risk** (`locRisk_const`): the risk of a location-equivariant estimator does
  not depend on `ξ`, so it equals its value `locRisk f ρ δ` at `ξ = 0`.
* **Structure of the equivariant class**: relative to any fixed equivariant `δ₀`,
  * `isLocEquivariant_iff_sub_invariant` — `δ` is equivariant iff `δ − δ₀` is
    translation-invariant;
  * `isLocInvariant_iff_factors_diffs` — a translation-invariant function is exactly a
    function of the differences `y = (x₁ − xₙ, …, x_{n−1} − xₙ)` (with a measurable
    factorization when the function is measurable);
  * `isLocEquivariant_iff_exists_diffs_rep` — combining the two, `δ` is equivariant iff
    `δ = δ₀ − v ∘ diffs` for some `v`.

The last item is what turns "minimize risk over the equivariant class" into "choose one
number `v(y)` per value of the maximal invariant", i.e. the conditional minimization
carried out in `LocationMRE`.

**Reference.** Classical location-equivariant estimation; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* `diffs` is indexed so that `n = m + 1` observations produce `m` differences. The
  classical statement splits into `n ≥ 2` (function of the differences) and `n = 1`
  (constant); here `m = 0` makes `Fin 0 → ℝ` a subsingleton, so the single statement
  covers both cases with no case split.
* The measurable factorization uses the explicit section `y ↦ Fin.snoc y 0` of `diffs`
  (appending a zero last coordinate), which is measurable and satisfies
  `diffs (Fin.snoc y 0) = y`; this is why the measurable version needs no descriptive
  set theory.
* `locRisk_const` needs no regularity of the density beyond what `locationFamily`
  already encodes: it is a pure change of variables `x ↦ x + ξ𝟙` under `lintegral_map`,
  so only measurability of `ρ` and `δ` enters. This is a (weakening) deviation from the
  classical statement, which assumes a density throughout.
* Losses are real functions pushed through `ENNReal.ofReal` inside `∫⁻` (junk-value
  discipline inherited from `locRisk`).

**Bibliographic comments.** Equivariant estimation of a location parameter, together with
the reduction to the differences as maximal invariant, is due to E. J. G. Pitman, "The
estimation of the location and scale parameters of a continuous population of any given
form," *Biometrika* **30** (1939), 391–421. The general group-theoretic formulation of
which this is the leading special case is due to G. A. Hunt and C. Stein (unpublished
manuscript, 1946), first reported in print by M. A. Girshick and L. J. Savage, "Bayes and
minimax estimates for quadratic loss functions," *Proc. Second Berkeley Symp. Math.
Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Location

variable {m n : ℕ}

/-! ### Elementary closure properties -/

/-- The difference statistic is measurable. -/
theorem measurable_diffs : Measurable (diffs : (Fin (m + 1) → ℝ) → Fin m → ℝ) := by
  sorry

/-- Appending a zero last coordinate is a section of `diffs`. -/
theorem diffs_snoc (y : Fin m → ℝ) : diffs (Fin.snoc y (0 : ℝ)) = y := by
  sorry

/-- Subtracting a constant preserves location equivariance. Together with
`locRisk_const` this is the whole content of the risk-unbiasedness of a minimum risk
equivariant estimator. -/
theorem IsLocEquivariant.sub_const {δ : (Fin n → ℝ) → ℝ} (hδ : IsLocEquivariant δ)
    (a : ℝ) : IsLocEquivariant fun x => δ x - a := by
  sorry

/-- Subtracting a translation-invariant function from an equivariant estimator leaves it
equivariant. -/
theorem IsLocEquivariant.sub_invariant {δ : (Fin n → ℝ) → ℝ} {u : (Fin n → ℝ) → ℝ}
    (hδ : IsLocEquivariant δ) (hu : IsLocInvariant u) :
    IsLocEquivariant fun x => δ x - u x := by
  sorry

/-! ### Constant risk -/

/-- **The risk of a location-equivariant estimator does not depend on the parameter.**
For loss `ρ(d − ξ)` the risk at `ξ` equals the risk at `ξ = 0`, namely `locRisk f ρ δ`.

Consequently "uniformly minimize the risk over the equivariant class" is the ordinary
minimization of one number, which is the definition of a minimum risk equivariant
estimator. The classical statement asserts the same constancy for the bias and the
variance; those follow by the identical change of variables and are not needed
downstream. -/
theorem locRisk_const (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ) (δ : (Fin n → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed only to run `lintegral_map`
    (hρ : Measurable ρ)
    -- LEAN-ONLY: measurability of the estimator; same role, no scope change
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator is location equivariant, `δ(x + a𝟙) = δ(x) + a`
    (hδeq : IsLocEquivariant δ)
    (ξ : ℝ) :
    ∫⁻ x, ENNReal.ofReal (ρ (δ x - ξ)) ∂(locationFamily f ξ) = locRisk f ρ δ := by
  sorry

/-! ### Structure of the equivariant class -/

/-- **An estimator is equivariant iff it differs from a fixed equivariant estimator by a
translation-invariant function.** -/
theorem isLocEquivariant_iff_sub_invariant {δ₀ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (h₀ : IsLocEquivariant δ₀)
    (δ : (Fin n → ℝ) → ℝ) :
    IsLocEquivariant δ ↔ IsLocInvariant fun x => δ x - δ₀ x := by
  sorry

/-- **A function of the data is translation-invariant iff it factors through the
differences.** For `m = 0` (a single observation) the target `Fin 0 → ℝ` is a
subsingleton, so the statement specialises to "invariant iff constant". -/
theorem isLocInvariant_iff_factors_diffs (u : (Fin (m + 1) → ℝ) → ℝ) :
    IsLocInvariant u ↔ ∃ v : (Fin m → ℝ) → ℝ, ∀ x, u x = v (diffs x) := by
  sorry

/-- Measurable version of the factorization through the differences: a measurable
translation-invariant function factors through `diffs` **measurably**. This is the form
consumed by the conditional-minimization argument, where the factor is integrated
against a conditional distribution. -/
theorem isLocInvariant_iff_factors_diffs_measurable (u : (Fin (m + 1) → ℝ) → ℝ) :
    (Measurable u ∧ IsLocInvariant u) ↔
      ∃ v : (Fin m → ℝ) → ℝ, Measurable v ∧ ∀ x, u x = v (diffs x) := by
  sorry

/-- **Representation of the equivariant class.** Relative to a fixed equivariant `δ₀`,
the equivariant estimators are exactly `δ₀ − v ∘ diffs` as `v` ranges over all functions
of the differences. -/
theorem isLocEquivariant_iff_exists_diffs_rep {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (h₀ : IsLocEquivariant δ₀)
    (δ : (Fin (m + 1) → ℝ) → ℝ) :
    IsLocEquivariant δ ↔ ∃ v : (Fin m → ℝ) → ℝ, ∀ x, δ x = δ₀ x - v (diffs x) := by
  sorry

/-- Measurable version of the representation of the equivariant class: measurable
equivariant estimators correspond to measurable functions of the differences. -/
theorem isLocEquivariant_iff_exists_diffs_rep_measurable {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (h₀ : IsLocEquivariant δ₀)
    -- LEAN-ONLY: measurability of the reference estimator; transfers measurability
    -- between `δ` and the factor `v`, no scope change
    (h₀meas : Measurable δ₀)
    (δ : (Fin (m + 1) → ℝ) → ℝ) :
    (Measurable δ ∧ IsLocEquivariant δ) ↔
      ∃ v : (Fin m → ℝ) → ℝ, Measurable v ∧ ∀ x, δ x = δ₀ x - v (diffs x) := by
  sorry

end Location

end StatLean.PointEstimation
