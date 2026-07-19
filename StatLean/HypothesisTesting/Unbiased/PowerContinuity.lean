import StatLean.HypothesisTesting.Tests.Defs
import StatLean.PointEstimation.ExponentialFamily.Defs

/-!
# Continuous power functions: boundary optimality ⇒ unbiased optimality

When every test has a **continuous** power function, unbiasedness of a test forces its power
to equal `α` on the *common boundary*
$$ \omega_B \;=\; \overline{\Theta_0} \cap \overline{\Theta_1} $$
of the null set `Θ₀` and the alternative set `Θ₁` (the set of points that are points or
limit points of both). Consequently the class of tests that are **similar on `ω_B`** contains
the class of unbiased level-`α` tests, and a test that is optimal in the larger (similar)
class and has level `α` is automatically UMP unbiased. This is the standard device that
converts the two-sided optimality problems into constrained Neyman–Pearson problems.

Main results:

* `isSimilar_boundary_of_isUnbiasedTest` — unbiased + continuous power ⇒ similar on `ω_B`;
* `isUMPU_of_isUMP_on_boundary` — optimal among boundary-similar tests + level `α` ⇒ UMPU;
* `continuous_power_expFamily` — power functions of exponential families are continuous on
  the interior of the natural parameter set (statement only here);
* `continuous_power_of_isCanonicalRepr` — the same for any continuous reparametrization.

**Reference.** Classical theory of unbiased tests; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The boundary set is supplied as data together with the defining equation
  `ωB = closure Θ₀ ∩ closure Θ₁`, rather than as a definition, so that callers may
  instantiate it with the concrete finite boundary sets (`{θ₀}`, `{θ₁, θ₂}`) that the
  one-parameter applications use, discharging the equation once.
* Continuity of the power function is quantified over *all* critical functions: this is what
  the source development assumes, and it is exactly what the exponential-family smoothness
  theorem delivers.
* The constant test `φ ≡ α` is the comparison test used to derive unbiasedness of the
  optimal test; it is a critical function precisely when `0 ≤ α ≤ 1`, whence the two
  side conditions on `α`.
* `continuous_power_expFamily` is stated as `ContinuousOn` over `interior E.natSet`: at
  boundary points of the natural parameter set the interchange of limit and integral can
  fail, and the source theorem is likewise restricted to the interior.

**Bibliographic comments.** Unbiasedness for testing problems, and the boundary-similarity
device recorded here, are due to J. Neyman and E. S. Pearson ("Contributions to the theory
of testing statistical hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37),
building on their earlier optimality theory ("On the problem of the most efficient tests of
statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337). The analyticity
of integrals against exponential-family densities, which supplies the continuity hypothesis,
goes back to the work systematized in O. Barndorff-Nielsen (*Information and Exponential
Families in Statistical Theory*, Wiley, 1978) and L. D. Brown (*Fundamentals of Statistical
Exponential Families*, IMS Lecture Notes 9, 1986).
-/

open MeasureTheory
open StatLean.PointEstimation

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Unbiased ⇒ similar on the boundary.**

If every power function is continuous, then a test that is unbiased at level `α` for
`Θ₀` against `Θ₁` has power exactly `α` on the common boundary
`ωB = closure Θ₀ ∩ closure Θ₁`: on `closure Θ₀` continuity propagates `power ≤ α`, on
`closure Θ₁` it propagates `α ≤ power`. -/
theorem isSimilar_boundary_of_isUnbiasedTest [TopologicalSpace Θ]
    {P : Θ → Measure 𝓧} {Θ₀ Θ₁ ωB : Set Θ} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the boundary set is the set of points that are points or limit points of
    -- both the null and the alternative set; classical boundary of a testing problem
    (hωB : ωB = closure Θ₀ ∩ closure Θ₁)
    -- USER-INPUT: every test has a continuous power function; the regularity hypothesis of
    -- the boundary device
    (hcont : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → Continuous (power P ψ))
    -- USER-INPUT: the test under consideration is a randomized test
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the test is unbiased at level `α`
    (hunb : IsUnbiasedTest P Θ₀ Θ₁ α φ) :
    IsSimilar P ωB α φ := by
  sorry

/-- **Boundary optimality ⇒ UMP unbiasedness.**

Assume every power function is continuous, and let `φ₀` be a level-`α` test that is similar
on the common boundary `ωB` and uniformly at least as powerful, on `Θ₁`, as every test that
is similar on `ωB`. Then `φ₀` is UMP unbiased at level `α`.

Two steps: the boundary-similar class contains the unbiased class
(`isSimilar_boundary_of_isUnbiasedTest`), so `φ₀` beats every unbiased competitor; and `φ₀`
is itself unbiased because the constant test `φ ≡ α` is boundary-similar.

The hypothesis `hsim` records that `φ₀` belongs to the class it is optimal in, as the source
formulation ("uniformly most powerful *among* the tests satisfying the boundary condition")
does; it is not consumed by the argument sketched above and may be dropped if a later
refactor prefers the minimal hypothesis set. -/
theorem isUMPU_of_isUMP_on_boundary [TopologicalSpace Θ]
    {P : Θ → Measure 𝓧} {Θ₀ Θ₁ ωB : Set Θ} {α : ℝ} {φ₀ : 𝓧 → ℝ}
    -- LEAN-ONLY: the family members are probability measures; needed so that the constant
    -- test `φ ≡ α` has power `α`, no scope change (every statistical model is such)
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the boundary set is the common boundary of null and alternative
    (hωB : ωB = closure Θ₀ ∩ closure Θ₁)
    -- USER-INPUT: every test has a continuous power function
    (hcont : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → Continuous (power P ψ))
    -- LEAN-ONLY: the level lies in `[0,1]`; needed for `φ ≡ α` to be a critical function
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    -- USER-INPUT: the candidate is a randomized test
    (hφ₀ : IsCriticalFn φ₀)
    -- USER-INPUT: the candidate has level `α` on the null set
    (hlevel : IsLevel P Θ₀ φ₀ α)
    -- USER-INPUT: the candidate is similar on the boundary
    (hsim : IsSimilar P ωB α φ₀)
    -- USER-INPUT: the candidate is uniformly most powerful among boundary-similar tests
    (hbest : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → IsSimilar P ωB α ψ →
      ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ₀ θ) :
    IsUMPU P Θ₀ Θ₁ α φ₀ := by
  sorry

/-- **Power functions of an exponential family are continuous on the interior of the natural
parameter set.**

For a bounded measurable `φ`, `η ↦ ∫ φ dP_η` is continuous (indeed real-analytic) on
`interior E.natSet`. Statement only in this file: the analytic input is the smoothness
theory of the log-partition function and of integrals against exponential-family densities
(see the point-estimation area's exponential-family smoothness development, which supplies
differentiation under the integral sign on the interior of the natural parameter set). -/
theorem continuous_power_expFamily {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V]
    (E : ExpFamily 𝓧 V) {φ : 𝓧 → ℝ}
    -- USER-INPUT: the integrand is a randomized test (bounded, measurable)
    (hφ : IsCriticalFn φ) :
    ContinuousOn (fun η => powerAgainst (E.P η) φ) (interior E.natSet) := by
  sorry

/-- **Continuity of the power function through a reparametrization.**

If `P'` is the canonical exponential family read through a continuous parameter map `ηmap`
taking values in the interior of the natural parameter set, then every power function of
`P'` is continuous — the hypothesis consumed by `isUMPU_of_isUMP_on_boundary`. -/
theorem continuous_power_of_isCanonicalRepr {Θ' V : Type*} [TopologicalSpace Θ']
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    {P' : Θ' → Measure 𝓧} {E : ExpFamily 𝓧 V} {ηmap : Θ' → V} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the model is a reparametrized canonical exponential family
    (hrepr : IsCanonicalRepr P' E ηmap)
    -- USER-INPUT: the parametrization is continuous; classical smooth-parametrization input
    (hcont : Continuous ηmap)
    -- USER-INPUT: the parametrization stays in the interior of the natural parameter set
    (hmem : ∀ θ, ηmap θ ∈ interior E.natSet)
    -- USER-INPUT: the integrand is a randomized test
    (hφ : IsCriticalFn φ) :
    Continuous (power P' φ) := by
  sorry

end StatLean.HypothesisTesting
