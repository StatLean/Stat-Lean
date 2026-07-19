import StatLean.HypothesisTesting.MLR.Defs
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Stochastic ordering and the monotone quantile coupling

Two laws on the real line are **stochastically ordered**, `F₁ ≤ F₀` pointwise, exactly when
they can be realized simultaneously on one probability space by two nondecreasing functions
of a single random variable, one everywhere below the other:
$$ F_1(x) \le F_0(x) \ \ \forall x \iff \exists\, f_0 \le f_1 \text{ nondecreasing, } V :
\ f_0(V) \sim F_0, \ \ f_1(V) \sim F_1 . $$
The realization is explicit: take `V` uniform on `(0,1)` and `f_i` the quantile function of
`F_i`, which is nondecreasing and satisfies `f_i(y) ≤ x ↔ y ≤ F_i(x)`; the ordering of the
distribution functions then transfers pointwise to the ordering of the quantiles.

Contents:
* `cdf_le_of_monotone_coupling` — a monotone coupling forces the ordering of the
  distribution functions (the easy direction);
* `exists_monotone_coupling_of_cdf_le` — the ordering produces a coupling, with `V`
  uniform on `(0,1)` (the substantive direction, stated constructively);
* `cdf_le_iff_exists_monotone_coupling` — the two combined.

**Proof formalization notes.**
* Distribution functions are written as `fun x => (μ (Set.Iic x)).toReal` rather than
  through a separate cumulative-distribution-function object, so that the statement is
  about the measures themselves and no compatibility lemma is needed.
* The coupling is stated with the uniform law written as
  `volume.restrict (Set.Icc 0 1)`, which makes `exists_monotone_coupling_of_cdf_le`
  constructive: the existential is over the two monotone maps only, not over the
  probability space. The endpoints carry no Lebesgue mass, so this is the uniform law on
  `(0,1)` of the classical statement; the closed interval is chosen to match the
  inverse-transform brick below.
* The intended construction takes `f_i := quantile F_i` for the shared left-continuous
  `quantile F p = sInf {x | p ≤ F x}`. Its Galois-connection lemma `quantile_le_iff`
  (`quantile F p ≤ x ↔ p ≤ F x`) turns the pointwise inequality of the distribution
  functions directly into `f₀ ≤ f₁` and gives monotonicity via `quantile_mono`, while
  `map_quantile_uniform` identifies the two pushforward laws.
* Measurability of the two maps is not part of the conclusion: it follows from
  monotonicity (`Monotone.measurable`), so the pushforwards are automatically defined.

**Bibliographic comments.** The equivalence between stochastic ordering and the existence
of a monotone coupling is due to E. L. Lehmann ("Ordered families of distributions,"
*Ann. Math. Statist.* **26** (1955), 399–419); it is the one-dimensional case of the
coupling theorem of V. Strassen ("The existence of probability measures with given
marginals," *Ann. Math. Statist.* **36** (1965), 423–439). Its use for families with
monotone likelihood ratio is systematized in S. Karlin and H. Rubin ("The theory of
decision procedures for distributions with monotone likelihood ratio," *Ann. Math.
Statist.* **27** (1956), 272–299).
-/

open MeasureTheory

namespace StatLean.HypothesisTesting

/-- **A monotone coupling orders the distribution functions.** If `f₀ ≤ f₁` are
nondecreasing and push a common law `ν` forward to `μ₀` and `μ₁`, then `μ₁` puts less mass
on every lower ray: `F₁ ≤ F₀` pointwise. -/
theorem cdf_le_of_monotone_coupling
    -- USER-INPUT: the two laws on the real line
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    -- USER-INPUT: the law of the coupling variable `V`
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    -- USER-INPUT: the two realizations
    (f₀ f₁ : ℝ → ℝ)
    -- USER-INPUT: both nondecreasing (measurability follows, so it is not assumed)
    (hf₀ : Monotone f₀) (hf₁ : Monotone f₁)
    -- USER-INPUT: one everywhere below the other — clause (a) of the classical statement
    (hle : ∀ v, f₀ v ≤ f₁ v)
    -- USER-INPUT: the two pushforwards are the given laws — clause (b)
    (hmap₀ : ν.map f₀ = μ₀) (hmap₁ : ν.map f₁ = μ₁) :
    ∀ x : ℝ, (μ₁ (Set.Iic x)).toReal ≤ (μ₀ (Set.Iic x)).toReal := by
  sorry

/-- **The stochastic ordering produces a monotone coupling.** If `F₁ ≤ F₀` pointwise then
both laws are realized as nondecreasing functions of a single variable uniform on `(0,1)`,
one everywhere below the other. Constructively: the two maps are the quantile functions of
`μ₀` and `μ₁`. -/
theorem exists_monotone_coupling_of_cdf_le
    -- USER-INPUT: the two laws on the real line
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    -- USER-INPUT: the stochastic ordering `F₁ ≤ F₀`, the hypothesis of the result
    (hcdf : ∀ x : ℝ, (μ₁ (Set.Iic x)).toReal ≤ (μ₀ (Set.Iic x)).toReal) :
    ∃ f₀ f₁ : ℝ → ℝ, Monotone f₀ ∧ Monotone f₁ ∧ (∀ v, f₀ v ≤ f₁ v) ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map f₀ = μ₀ ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map f₁ = μ₁ := by
  sorry

/-- **The characterization.** Stochastic ordering of two laws on the real line is
equivalent to the existence of a monotone coupling of them. -/
theorem cdf_le_iff_exists_monotone_coupling
    -- USER-INPUT: the two laws on the real line
    (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] :
    (∀ x : ℝ, (μ₁ (Set.Iic x)).toReal ≤ (μ₀ (Set.Iic x)).toReal) ↔
      ∃ (ν : Measure ℝ) (_ : IsProbabilityMeasure ν) (f₀ f₁ : ℝ → ℝ),
        Monotone f₀ ∧ Monotone f₁ ∧ (∀ v, f₀ v ≤ f₁ v) ∧
          ν.map f₀ = μ₀ ∧ ν.map f₁ = μ₁ := by
  sorry

end StatLean.HypothesisTesting
