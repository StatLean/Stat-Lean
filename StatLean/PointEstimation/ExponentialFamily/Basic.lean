import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Notation

/-!
# Exponential families — basic structural properties

The elementary facts that make the data model of `ExponentialFamily.Defs` usable:

* `ExpFamily.natSet_convex` — the natural parameter set is convex (Hölder);
* `ExpFamily.isProbabilityMeasure_P` — members indexed by the natural parameter set are
  probability measures (for a nonzero reference measure);
* `ExpFamily.P_eq_zero_of_notMem` — the junk convention: off the natural parameter set the
  member is the zero measure;
* `ExpFamily.P_eq_withDensity` — the member in explicit density form,
  `dP_η/dν = exp(⟨η, T⟩ − A(η))`;
* `ExpFamily.P_ofDensity_eq` — the classical presentation `exp(⟨η, T⟩ − A(η))·h dμ` recovered
  for families built with `ExpFamily.ofDensity`;
* `ExpFamily.pow` / `ExpFamily.natSet_pow` / `ExpFamily.pi_P_eq_pow_P` — stability under
  i.i.d. sampling: the `n`-fold product of members is the member of the product family whose
  natural statistic is `x ↦ ∑ i, T(xᵢ)`.

**Reference.** Classical exponential-family theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* Convexity of the natural parameter set is Hölder's inequality applied to the factorization
  `exp⟨a·η₀ + b·η₁, T⟩ = (exp⟨η₀, T⟩)^a · (exp⟨η₁, T⟩)^b` with conjugate exponents `1/a`,
  `1/b`. It holds for an arbitrary reference measure — no finiteness assumption.
* `isProbabilityMeasure_P` genuinely needs `E.base ≠ 0`: for the zero reference measure every
  member is the zero measure. This is the only place a nondegeneracy input is unavoidable
  among the density lemmas — `P_eq_withDensity` holds unconditionally because both sides
  collapse to `0` when `E.base = 0` (there `A(η) = log 0 = 0` and the normalizer is `0`).
* The i.i.d. statement is given as a **measure equality** rather than as an
  `IsCanonicalRepr`: the equality is the reusable form (it rewrites under any parametrization),
  and `IsCanonicalRepr (fun θ : Ξ' => Measure.pi fun _ => E.P θ) (E.pow n) (↑·)` follows from
  it by `fun θ => pi_P_eq_pow_P …` for any `Ξ' ⊆ E.natSet`.
* `pow` needs `[BorelSpace V] [SecondCountableTopology V]` only to know that a finite sum in
  `V` is measurable (`MeasurableAdd₂` is derived from `ContinuousAdd` there); both hold in
  every intended instantiation (`V = ℝ`, `V = EuclideanSpace ℝ (Fin s)`).
* `natSet_pow` is stated as the inclusion `E.natSet ⊆ (E.pow n).natSet`, which is the
  direction consumers need and is true for every `n` (including `n = 0`, where the product
  reference measure is a Dirac mass and the right-hand side is everything). The reverse
  inclusion also holds for `n ≥ 1` but is not needed.

**Bibliographic comments.** Exponential families originate with R. A. Fisher ("Two new
properties of mathematical likelihood," *Proc. R. Soc. Lond. A* **144** (1934), 285–307),
G. Darmois ("Sur les lois de probabilité à estimation exhaustive," *C. R. Acad. Sci. Paris*
**200** (1935), 1265–1266), B. O. Koopman ("On distributions admitting a sufficient
statistic," *Trans. Amer. Math. Soc.* **39** (1936), 399–409) and E. J. G. Pitman
("Sufficient statistics and intrinsic accuracy," *Proc. Camb. Phil. Soc.* **32** (1936),
567–579). Convexity of the natural parameter set and the closure of the class under
convolution of independent components are part of the systematic treatments of
O. Barndorff-Nielsen (*Information and Exponential Families in Statistical Theory*, Wiley,
1978) and L. D. Brown (*Fundamentals of Statistical Exponential Families*, IMS Lecture
Notes 9, 1986).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

section Members

variable [OpensMeasurableSpace V]

/-- The natural parameter set is **convex**. -/
theorem natSet_convex (E : ExpFamily 𝓧 V) : Convex ℝ E.natSet := by
  sorry

/-- Members indexed by the natural parameter set are **probability measures**. -/
theorem isProbabilityMeasure_P (E : ExpFamily 𝓧 V) {η : V}
    -- USER-INPUT: nondegenerate reference measure; without it every member is the zero
    -- measure and the normalization is vacuous
    (hbase : E.base ≠ 0)
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet) :
    IsProbabilityMeasure (E.P η) := by
  sorry

/-- **Junk convention**: off the natural parameter set the member is the zero measure. -/
theorem P_eq_zero_of_notMem (E : ExpFamily 𝓧 V) {η : V}
    -- LEAN-ONLY: the parameter is outside the domain of definition; records the junk value
    -- inherited from `Measure.tilted`, so that consumers never need a side condition
    (hη : η ∉ E.natSet) :
    E.P η = 0 := by
  sorry

/-- **Explicit density form** of a member: `dP_η/dν = exp(⟨η, T⟩ − A(η))`. -/
theorem P_eq_withDensity (E : ExpFamily 𝓧 V) {η : V}
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet) :
    E.P η = E.base.withDensity
      fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)) := by
  sorry

/-- **Classical presentation**: for a family built by absorbing a carrier `h` into the
reference measure, the member has density `exp(⟨η, T x⟩ − A(η))·h(x)` with respect to `μ`. -/
theorem P_ofDensity_eq (μ : Measure 𝓧) {h : 𝓧 → ℝ≥0∞}
    -- USER-INPUT: measurable carrier; the classical presentation's `h`
    (hh : Measurable h)
    {T : 𝓧 → V}
    -- USER-INPUT: measurable natural statistic
    (hT : Measurable T) {η : V}
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ (ofDensity μ h T hT).natSet) :
    (ofDensity μ h T hT).P η
      = μ.withDensity fun x =>
          ENNReal.ofReal (Real.exp (⟪η, T x⟫_ℝ - (ofDensity μ h T hT).logPartition η)) * h x := by
  sorry

end Members

section Product

variable [BorelSpace V] [SecondCountableTopology V]

/-- The **`n`-fold i.i.d. product family**: the reference measure is the product of `n` copies
of `E.base` and the natural statistic is `x ↦ ∑ i, T(xᵢ)`. This is the exponential family in
which an i.i.d. sample of size `n` from `E` lives; its log-partition function is `n·A(η)`. -/
noncomputable def pow (E : ExpFamily 𝓧 V) (n : ℕ) : ExpFamily (Fin n → 𝓧) V where
  base := Measure.pi fun _ => E.base
  stat := fun x => ∑ i, E.stat (x i)
  stat_meas := by
    have h : ∀ i : Fin n, Measurable fun x : Fin n → 𝓧 => E.stat (x i) := fun i =>
      E.stat_meas.comp (measurable_pi_apply i)
    exact Finset.measurable_sum Finset.univ fun i _ => h i

/-- The natural parameter set of the product family contains that of the one-observation
family. -/
theorem natSet_pow (E : ExpFamily 𝓧 V)
    -- LEAN-ONLY: σ-finiteness of the reference measure, so that the product measure has its
    -- expected Tonelli behaviour; every dominated statistical model satisfies it
    [SigmaFinite E.base] (n : ℕ) :
    E.natSet ⊆ (E.pow n).natSet := by
  sorry

/-- **Stability under i.i.d. sampling**: the `n`-fold product of the member `P_η` is the
member of the product family at the same natural parameter. -/
theorem pi_P_eq_pow_P (E : ExpFamily 𝓧 V)
    -- LEAN-ONLY: σ-finiteness of the reference measure, needed for Tonelli on the product
    [SigmaFinite E.base] (n : ℕ) {η : V}
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet) :
    (Measure.pi fun _ : Fin n => E.P η) = (E.pow n).P η := by
  sorry

end Product

end ExpFamily

end StatLean.PointEstimation
