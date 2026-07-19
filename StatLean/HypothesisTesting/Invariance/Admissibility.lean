import StatLean.HypothesisTesting.Tests.Defs
import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Convex.Basic

/-!
# Admissibility of convex acceptance regions in an exponential family

Optimality within a restricted class — invariant tests, say — does not by itself make a
test admissible: a uniformly most powerful invariant test can be beaten uniformly by a
test that is not invariant. Admissibility therefore has to be established separately, and
the classical route for exponential families is *convexity of the acceptance region*.

Two notions are distinguished. A test `φ₀` is **`α`-admissible** against a class of
alternatives when no level-`α` competitor has power at least as large everywhere on that
class without matching it there. It is **d-admissible** when the two-sided comparison —
power at least as large on the alternatives *and* at most as large on the null — forces
equality of the power functions throughout. The second is the decision-theoretic notion;
neither implies the other in general.

The main theorem says: for an exponential family on the natural-statistic scale, if the
acceptance region `A₀` is **closed and convex**, and if every open half-space missing `A₀`
points in a direction along which the alternative class contains an unbounded ray, then
any competing acceptance region that is uniformly no worse than `A₀` on the alternatives
is contained in `A₀` up to a null set. The mechanism is geometric: a competitor
protruding from a closed convex set can be separated from it by a hyperplane, and pushing
the natural parameter to infinity along the direction of that hyperplane makes the
protruding part dominate the likelihood, so the competitor would have to be *strictly*
worse somewhere on the alternatives. Admissibility of `φ₀` follows; if in addition the
size `α` is attained at a point of the closure of the null class, the sharper
`α`-admissibility follows too.

**Main results.**
* `IsDAdmissible`, `IsAlphaAdmissible` — the two admissibility notions;
* `statScaleFamily`, `statScaleBase` — the induced family and dominating measure on the
  natural-statistic scale;
* `acceptance_subset_of_power_le` — closed convex acceptance region: any uniformly
  no-worse competitor is a.e. contained in it;
* `isDAdmissible_of_convex_acceptance`, `isAlphaAdmissible_of_size_attained` — the two
  admissibility conclusions.

**Proof formalization notes.**
* Everything is stated **on the natural-statistic scale**: acceptance regions are subsets
  of `V = EuclideanSpace ℝ (Fin s)`, the model is the family of laws of the natural
  statistic (`statScaleFamily`), and the null set in the conclusion is measured by the
  image of the reference measure (`statScaleBase`). The source identifies the sample space
  with the statistic scale for this theorem; the sample-space reading is the pullback of
  the statement along the natural statistic.
* The ray condition is transcribed verbatim: *whenever* the open half-space
  `{t : ⟨a, t⟩ > c}` misses `A₀`, there is a point of the alternative class and a sequence
  of scalars tending to infinity keeping `θ* + λₙ a` in the alternative class.
* `IsDAdmissible` quantifies over **all** critical functions, with no level restriction —
  the level enters only in `IsAlphaAdmissible`. This matches the source's two definitions.
* `φ₀` is the **nonrandomized** indicator of the complement of `A₀`. The source notes that
  competitors may be randomized but that nonrandomization of `φ₀` is essential, which is
  why the acceptance region — not merely a critical function — is the primitive here.
* In the `α`-admissibility corollary, `θ₀` is required to lie in the natural parameter set
  as well as in the closure of the null class: this is the content of the source's
  "finite point", i.e. an actual parameter rather than a limit at infinity. Continuity of
  the power function in the natural parameter, used to pass from `θ₀` back into the null
  class, is a property of exponential families and is therefore *not* a hypothesis: it is
  a derivation obligation inside the proof.
* The separation step is the geometric Hahn–Banach theorem for a closed convex set and an
  exterior point (`geometric_hahn_banach_closed_point` in Mathlib's
  `Analysis.LocallyConvex.Separation`).

**Bibliographic comments.** Admissibility of tests with convex acceptance regions in
exponential families, and the ray condition delimiting the alternative classes against
which admissibility holds, come from the work of C. Stein ("The admissibility of Hotelling's
$T^2$-test," *Ann. Math. Statist.* **27** (1956), 616–623) and A. Birnbaum
("Characterizations of complete classes of tests of some multiparametric hypotheses, with
applications to likelihood ratio tests," *Ann. Math. Statist.* **26** (1955), 21–36); the
complete-class theory for such problems was extended by K. Matthes and D. R. Truax
("Tests of composite hypotheses for the multivariate exponential family," *Ann. Math.
Statist.* **38** (1967), 681–697). Admissibility of the one- and two-sided $t$-tests
against all invariant classes of alternatives is due to E. L. Lehmann and C. Stein
(1953), building on their earlier work on non-parametric hypotheses (*Ann. Math. Statist.*
**20** (1949), 28–45).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (ExpFamily)

/-! ## The two admissibility notions -/

section Admissible

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **d-admissibility** of `φ₀` for testing `Θ_H` against a class of alternatives `Θ'`:
if a critical function is at least as powerful as `φ₀` everywhere on `Θ'` and at most as
powerful everywhere on `Θ_H`, then its power function agrees with that of `φ₀` throughout
`Θ_H ∪ Θ'`. No level restriction is imposed on the competitor. -/
def IsDAdmissible (P : Θ → Measure 𝓧) (Θ_H Θ' : Set Θ) (φ₀ : 𝓧 → ℝ) : Prop :=
  ∀ φ : 𝓧 → ℝ, IsCriticalFn φ →
    (∀ θ ∈ Θ', power P φ₀ θ ≤ power P φ θ) →
    (∀ θ ∈ Θ_H, power P φ θ ≤ power P φ₀ θ) →
    ∀ θ ∈ Θ_H ∪ Θ', power P φ θ = power P φ₀ θ

/-- **`α`-admissibility** of `φ₀` for testing `Θ_H` against a class of alternatives `Θ'`:
every level-`α` competitor that is at least as powerful as `φ₀` everywhere on `Θ'` in fact
has the same power as `φ₀` there. -/
def IsAlphaAdmissible (P : Θ → Measure 𝓧) (Θ_H Θ' : Set Θ) (α : ℝ) (φ₀ : 𝓧 → ℝ) : Prop :=
  ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsLevel P Θ_H φ α →
    (∀ θ ∈ Θ', power P φ₀ θ ≤ power P φ θ) →
    ∀ θ ∈ Θ', power P φ θ = power P φ₀ θ

end Admissible

/-! ## The exponential family on the natural-statistic scale -/

section StatScale

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {s : ℕ}

/-- The **induced family on the natural-statistic scale**: the law of the natural
statistic under the canonical member indexed by `η`. Off the natural parameter set the
member measure is the zero measure, and so is its image. -/
noncomputable def statScaleFamily (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (η : EuclideanSpace ℝ (Fin s)) : Measure (EuclideanSpace ℝ (Fin s)) :=
  (E.P η).map E.stat

/-- The **dominating measure on the natural-statistic scale**: the image of the reference
measure of the family under the natural statistic. Null sets for it are the sets the
admissibility conclusion is allowed to ignore. -/
noncomputable def statScaleBase (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) :
    Measure (EuclideanSpace ℝ (Fin s)) :=
  E.base.map E.stat

end StatScale

/-! ## Closed convex acceptance regions are admissible -/

section Convex

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {s : ℕ}

/-- **A competitor no worse than a closed convex acceptance region is contained in it.**
If `A₀` is closed and convex and every open half-space missing `A₀` points along a
direction in which the alternative class contains an unbounded ray, then any acceptance
region `A` whose acceptance probability is everywhere on the alternatives at most that of
`A₀` satisfies `A ⊆ A₀` up to a null set. -/
theorem acceptance_subset_of_power_le (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ A : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the two acceptance regions, needed to speak of their
    -- probabilities at all
    (hA₀meas : MeasurableSet A₀) (hAmeas : MeasurableSet A)
    -- USER-INPUT: the ray condition — whenever an open half-space misses `A₀`, the
    -- alternative class contains an unbounded ray in the direction of that half-space
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    -- USER-INPUT: `A` is nowhere on the alternatives a better acceptance region than `A₀`
    (hpow : ∀ θ ∈ Θ', statScaleFamily E θ A ≤ statScaleFamily E θ A₀) :
    statScaleBase E (A \ A₀) = 0 := by
  sorry

/-- **A closed convex acceptance region is d-admissible.** -/
theorem isDAdmissible_of_convex_acceptance (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the acceptance region
    (hA₀meas : MeasurableSet A₀)
    -- USER-INPUT: the ray condition
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ') :
    IsDAdmissible (statScaleFamily E) Θ_H Θ'
      (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
  sorry

/-- **A closed convex acceptance region whose size is attained is `α`-admissible.** If in
addition the size of the test is `α` and there is an actual parameter point in the closure
of the null class at which the power equals `α`, then the test is `α`-admissible. -/
theorem isAlphaAdmissible_of_size_attained (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))} {α : ℝ}
    {θ₀ : EuclideanSpace ℝ (Fin s)}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the acceptance region
    (hA₀meas : MeasurableSet A₀)
    -- USER-INPUT: the ray condition
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    -- USER-INPUT: the test has level `α` on the null class
    (hlevel : IsLevel (statScaleFamily E) Θ_H (A₀ᶜ.indicator fun _ => (1 : ℝ)) α)
    -- USER-INPUT: the size is attained at a point of the closure of the null class which
    -- is an actual parameter (the source's "finite point")
    (hθ₀closure : θ₀ ∈ closure Θ_H) (hθ₀nat : θ₀ ∈ E.natSet)
    (hθ₀size : power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) θ₀ = α) :
    IsAlphaAdmissible (statScaleFamily E) Θ_H Θ' α
      (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
  sorry

end Convex

end StatLean.HypothesisTesting
