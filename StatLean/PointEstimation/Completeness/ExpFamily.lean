import StatLean.PointEstimation.Completeness.Defs
import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Notation

/-!
# Completeness of the natural statistic of an exponential family

The natural statistic of a canonical exponential family is complete as soon as the parameter
set has nonempty interior. Suppose `f` is integrable with `E_η[f(T)] = 0` for every `η` in the
parameter set. On the statistic's scale this reads
$$ \int f(t)\,e^{\langle \eta, t\rangle}\,d\nu_T(t) \;=\; 0, $$
so the two finite measures obtained by weighting `ν_T` with the positive and the negative part
of `f` have the same Laplace transform on a set with nonempty interior. Uniqueness of Laplace
transforms on an open set forces the two measures to coincide, i.e. `f = 0` almost
everywhere.

* `isCompleteStat_of_interior_nonempty` — the multivariate statement;
* `isCompleteStat_of_interior_nonempty_real` — its one-dimensional specialization.

**Reference.** Classical exponential-family and completeness theory; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* Only **nonempty interior** of the parameter set is assumed, not the full rank condition.
  Affine independence of the natural statistic — the other half of `ExpFamily.FullRank` — is
  what minimality of `T` needs; completeness does not use it, and assuming it would weaken the
  theorem for no gain. `ExpFamily.FullRank.2.1` supplies the interior hypothesis directly for
  callers holding the classical full-rank condition.
* No nondegeneracy hypothesis on the reference measure is needed: if `E.base = 0` then every
  member and hence every law of the statistic is the zero measure, and the conclusion
  `f =ᵐ[0] 0` is vacuously true.
* The intended route is the Laplace/moment-generating-function uniqueness bricks being
  developed in the area's `ForMathlib` layer —
  `ext_of_integral_exp_eqOn` and `ae_eq_zero_of_integral_exp_smul_eq_zero` in the
  one-dimensional case, `ext_of_integral_exp_inner_eqOn` and
  `ae_eq_zero_of_integral_exp_inner_eq_zero` in the multivariate case. Those modules are not
  imported here: with `sorry` bodies the import would add nothing but a scheduling
  dependency, so the closing session should add
  `import StatLean.PointEstimation.ForMathlib.MGFUniqueness` and
  `import StatLean.PointEstimation.ForMathlib.MGFUniquenessPi` when it fills the proofs.
* The conclusion is stated as `IsCompleteFamily` applied to the laws of the natural statistic;
  this unfolds definitionally to `IsCompleteStat (fun θ : Ξ' => E.P θ) E.stat`, so either
  spelling may be used by consumers.
* The multivariate statement is given on `EuclideanSpace ℝ (Fin s)` rather than for an
  abstract inner-product space: the Laplace-uniqueness argument is a statement about finitely
  many real parameters, and the concrete space is what carries the required measurable-space
  and Borel instances.

**Bibliographic comments.** Completeness of the natural statistic of a full-rank exponential
family is due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased
estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236). Modern treatments,
including the Laplace-transform argument used here, are in O. Barndorff-Nielsen (*Information
and Exponential Families in Statistical Theory*, Wiley, 1978, Lemma 8.2) and L. D. Brown
(*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9, 1986, Thm 2.12).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Completeness of the natural statistic**: for a canonical exponential family on
`EuclideanSpace ℝ (Fin s)` whose parameter set has nonempty interior, the family of laws of
the natural statistic is complete. -/
theorem isCompleteStat_of_interior_nonempty {s : ℕ}
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) (Ξ' : Set (EuclideanSpace ℝ (Fin s)))
    -- USER-INPUT: the parameter set lies in the natural parameter set, so every member is a
    -- genuine probability measure of the family
    (hΞ : Ξ' ⊆ E.natSet)
    -- USER-INPUT: the parameter set has nonempty interior; the classical rank condition, and
    -- exactly the openness that Laplace-transform uniqueness requires
    (hint : (interior Ξ').Nonempty) :
    IsCompleteFamily fun θ : Ξ' => (E.P (θ : EuclideanSpace ℝ (Fin s))).map E.stat := by
  sorry

/-- One-dimensional specialization of `isCompleteStat_of_interior_nonempty`: a real natural
statistic is complete whenever the parameter set has nonempty interior in the line. -/
theorem isCompleteStat_of_interior_nonempty_real (E : ExpFamily 𝓧 ℝ) (Ξ' : Set ℝ)
    -- USER-INPUT: the parameter set lies in the natural parameter set
    (hΞ : Ξ' ⊆ E.natSet)
    -- USER-INPUT: the parameter set has nonempty interior; classically, it contains an
    -- interval of positive length
    (hint : (interior Ξ').Nonempty) :
    IsCompleteFamily fun θ : Ξ' => (E.P (θ : ℝ)).map E.stat := by
  sorry

end StatLean.PointEstimation
