import StatLean.HypothesisTesting.Invariance.AlmostInvariance
import StatLean.PointEstimation.Sufficiency.Defs
import StatLean.PointEstimation.Completeness.Defs

/-!
# Invariance after sufficiency: almost invariance, power invariance, and legitimacy

Restricting attention to invariant tests is a departure from comparing tests purely by
their power functions, so it is natural to ask what invariance means *at the level of
power functions*. One implication is immediate: an invariant — indeed an almost invariant
— test has a power function invariant under the induced group. The converse fails in
general, but it holds once the problem has first been reduced to a **sufficient statistic
whose family of laws is boundedly complete**. That is the content of the first result
below, and it is what makes almost invariance the right class to work with.

Two consequences follow. First, a test that is UMP among almost invariant tests based on
the sufficient statistic is optimal in a much larger class: among *all* tests of the
original data whose power function depends on the parameter only through a maximal
invariant. Second — and this is the practical point — reducing by sufficiency **before**
applying invariance is legitimate: every invariant test of the raw data is matched, in
power, by an almost invariant (and, under the structural conditions for almost invariance,
by a genuinely invariant) test of the statistic, so nothing is lost by performing the two
reductions in that order.

**Main results.**
* `power_invariant_iff_almostInvariant` — for a boundedly complete family of laws of the
  statistic, invariance of the power function ⟺ almost invariance of the test;
* `isUMP_of_isUMPAlmostInvariant_sufficient` — a UMP almost invariant test based on a
  sufficient statistic is UMP among all tests with power depending only on a maximal
  invariant of the parameter;
* `exists_almostInvariant_on_stat_of_invariant`,
  `exists_invariant_on_stat_of_invariant`,
  `isUMPInvariant_comp_of_isUMPInvariant_stat` — the three parts of the legitimacy of the
  sufficiency-then-invariance reduction.

**Proof formalization notes.**
* In the first result the group acts on the **statistic space** `𝓣`, and the relevant
  family is the family of laws `statLaw P T`. Bounded completeness is the point-estimation
  predicate `IsBoundedlyCompleteStat`, applied to that family; the invariance of the
  reduced problem is `IsInvariantModel` for `statLaw P T`. Sufficiency is *not* assumed
  here — the source's lemma needs only bounded completeness of the family of laws.
* Almost invariance of a test of the statistic is taken "a.e. `P^T`", i.e. with respect to
  every member `statLaw P T θ`, matching the source's exceptional-set convention.
* The induced group on the statistic space is supplied as a `MulAction G 𝓣` instance
  together with the intertwining law `T (g·x) = g·(T x)` (`hTcompat`). This is a
  **LEAN-ONLY** packaging of the source's setup, which imposes the compatibility condition
  `T x₁ = T x₂ ⟹ T(g x₁) = T(g x₂)` and *then defines* the induced transformation by
  `g̃ (T x) = T (g x)`; supplying the action as data plus the intertwining identity is the
  same content once the induced group exists, which is exactly what the condition asserts.
* Maximal invariance of the parameter-space map `v` is written inline as the two set-level
  conditions, so no measurable structure is demanded of the parameter space.

**Bibliographic comments.** The interplay of sufficiency and invariance — in particular the
legitimacy of reducing by sufficiency first — was settled in the invariance program of
G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses," unpublished
manuscript, 1946) and C. Stein ("Some problems in multivariate analysis, Part I,"
Technical Report 6, Department of Statistics, Stanford University, 1956), and developed in
E. L. Lehmann's lecture tradition of the 1950s. A definitive treatment of when the two
reductions commute is due to W. J. Hall, R. A. Wijsman and J. K. Ghosh ("The relationship
between sufficiency and invariance with applications in sequential analysis," *Ann. Math.
Statist.* **36** (1965), 575–614). Bounded completeness as the hypothesis converting
power-function invariance into almost invariance of the test traces to E. L. Lehmann and
H. Scheffé ("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10**
(1950), 305–340).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel statLaw HasSufficientKernel
  IsBoundedlyCompleteStat)

variable {G Θ 𝓧 𝓣 𝓥 : Type*} [Group G] [MeasurableSpace 𝓧] [MeasurableSpace 𝓣]

/-! ## Power invariance versus almost invariance -/

/-- **Invariant power function ⟺ almost invariant test**, for a boundedly complete family
of laws of the statistic. One direction is unconditional; the converse is exactly where
bounded completeness is used. -/
theorem power_invariant_iff_almostInvariant [MulAction G 𝓣] [MulAction G Θ]
    {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → 𝓣} {ψ : 𝓣 → ℝ}
    -- USER-INPUT: the family of laws of `T` is boundedly complete
    (hbc : IsBoundedlyCompleteStat P T)
    -- USER-INPUT: the reduced problem is invariant under the action on the statistic space
    (hQ : IsInvariantModel (G := G) (statLaw P T))
    -- USER-INPUT: `ψ` is a critical function on the statistic space
    (hψ : IsCriticalFn ψ) :
    (∀ (g : G) (θ : Θ), power (statLaw P T) ψ (g • θ) = power (statLaw P T) ψ θ) ↔
      ∀ θ, IsAlmostInvariant G (statLaw P T θ) ψ := by
  sorry

/-- **A UMP almost invariant test based on a sufficient statistic is UMP in the class of
all tests whose power depends only on a maximal invariant of the parameter.** -/
theorem isUMP_of_isUMPAlmostInvariant_sufficient [MulAction G 𝓣] [MulAction G Θ]
    {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → 𝓣} {v : Θ → 𝓥}
    {Θ₀ Θ₁ : Set Θ} {α : ℝ} {ψ₀ : 𝓣 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic, needed to transport tests and laws
    (hTmeas : Measurable T)
    -- USER-INPUT: the family of laws of `T` is boundedly complete
    (hbc : IsBoundedlyCompleteStat P T)
    -- USER-INPUT: the reduced problem is invariant under the action on the statistic space
    (hQ : IsInvariantModel (G := G) (statLaw P T))
    -- USER-INPUT: `v` is invariant under the induced parameter action
    (hv_inv : ∀ (g : G) (θ : Θ), v (g • θ) = v θ)
    -- USER-INPUT: `v` separates the induced orbits (maximal invariance of `v`)
    (hv_max : ∀ θ θ' : Θ, v θ = v θ' → ∃ g : G, θ' = g • θ)
    -- USER-INPUT: `ψ₀` is UMP among almost invariant level-`α` tests of the statistic
    (hψ₀ : IsUMPAlmostInvariant G (statLaw P T) Θ₀ Θ₁ α ψ₀) :
    IsCriticalFn (fun x => ψ₀ (T x)) ∧
      ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsLevel P Θ₀ φ α →
        (∀ θ θ' : Θ, v θ = v θ' → power P φ θ = power P φ θ') →
        ∀ θ ∈ Θ₁, power P φ θ ≤ power P (fun x => ψ₀ (T x)) θ := by
  sorry

/-! ## Legitimacy of reducing by sufficiency before invariance -/

section Legitimacy

variable [MulAction G 𝓧] [MulAction G 𝓣] [MulAction G Θ] {P : Θ → Measure 𝓧} {T : 𝓧 → 𝓣}

/-- **(i)** Every invariant test of the raw data is matched in power by an almost
invariant test based on the sufficient statistic. -/
theorem exists_almostInvariant_on_stat_of_invariant [∀ θ, IsProbabilityMeasure (P θ)]
    {φ : 𝓧 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic
    (hTmeas : Measurable T)
    -- USER-INPUT: the model is invariant under the sample-space action
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the statistic intertwines the two actions, `T (g·x) = g·(T x)`;
    -- this is the source's compatibility condition together with the definition of the
    -- induced group on the statistic space
    (hTcompat : ∀ (g : G) (x : 𝓧), T (g • x) = g • T x)
    -- USER-INPUT: `φ` is an invariant critical function of the raw data
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ) :
    ∃ ψ : 𝓣 → ℝ, IsCriticalFn ψ ∧ (∀ θ, IsAlmostInvariant G (statLaw P T θ) ψ) ∧
      ∀ θ, power (statLaw P T) ψ θ = power P φ θ := by
  sorry

/-- **(ii)** Under the structural conditions making almost invariance equivalent to
invariance on the statistic space, the matching test of part (i) can be taken invariant. -/
theorem exists_invariant_on_stat_of_invariant [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓣] [∀ θ, IsProbabilityMeasure (P θ)] {ν : Measure G} [SigmaFinite ν]
    {μT : Measure 𝓣} [SigmaFinite μT] {φ : 𝓧 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic
    (hTmeas : Measurable T)
    -- USER-INPUT: the model is invariant under the sample-space action
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the statistic intertwines the two actions
    (hTcompat : ∀ (g : G) (x : 𝓧), T (g • x) = g • T x)
    -- USER-INPUT: the group carries a nonzero σ-finite measure with right-translation
    -- stable null sets
    (hν0 : ν ≠ 0)
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `μT` is a σ-finite measure equivalent to the family of laws of `T`
    (hdom : ∀ θ, statLaw P T θ ≪ μT)
    (hequiv : ∀ B : Set 𝓣, MeasurableSet B → (∀ θ, statLaw P T θ B = 0) → μT B = 0)
    -- USER-INPUT: `φ` is an invariant critical function of the raw data
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ) :
    ∃ ψ : 𝓣 → ℝ, IsCriticalFn ψ ∧ IsInvariantTest G ψ ∧
      ∀ θ, power (statLaw P T) ψ θ = power P φ θ := by
  sorry

/-- **(iii)** A test UMP among invariant tests of the sufficient statistic is UMP among
all invariant tests of the raw data — the sufficiency-then-invariance reduction is
legitimate. -/
theorem isUMPInvariant_comp_of_isUMPInvariant_stat [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓣] [∀ θ, IsProbabilityMeasure (P θ)] {ν : Measure G} [SigmaFinite ν]
    {μT : Measure 𝓣} [SigmaFinite μT] {Θ₀ Θ₁ : Set Θ} {α : ℝ} {ψ₀ : 𝓣 → ℝ}
    -- USER-INPUT: `T` is sufficient for the model
    (hsuf : HasSufficientKernel P T)
    -- LEAN-ONLY: measurability of the statistic
    (hTmeas : Measurable T)
    -- USER-INPUT: the model is invariant under the sample-space action
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the statistic intertwines the two actions
    (hTcompat : ∀ (g : G) (x : 𝓧), T (g • x) = g • T x)
    -- USER-INPUT: the group carries a nonzero σ-finite measure with right-translation
    -- stable null sets
    (hν0 : ν ≠ 0)
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `μT` is a σ-finite measure equivalent to the family of laws of `T`
    (hdom : ∀ θ, statLaw P T θ ≪ μT)
    (hequiv : ∀ B : Set 𝓣, MeasurableSet B → (∀ θ, statLaw P T θ B = 0) → μT B = 0)
    -- USER-INPUT: `ψ₀` is UMP among invariant level-`α` tests of the statistic
    (hψ₀ : IsUMPInvariant G (statLaw P T) Θ₀ Θ₁ α ψ₀) :
    IsUMPInvariant G P Θ₀ Θ₁ α (fun x => ψ₀ (T x)) := by
  sorry

end Legitimacy

end StatLean.HypothesisTesting
