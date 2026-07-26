import StatLean.HypothesisTesting.Invariance.Defs

/-!
# Almost invariance and its equivalence with invariance

A test is **almost invariant** when, for each group element separately, it is unchanged
along the action off a null set — the exceptional set being allowed to depend on the group
element. This is strictly weaker than invariance in general, and it is the class that
naturally appears when invariance is compared with unbiasedness or reached through a
sufficiency reduction.

The central result says that under two structural conditions the two notions coincide up
to a null set:

* **joint measurability** of the action, i.e. for every measurable `A` the set of pairs
  `(x, g)` with `g·x ∈ A` is product-measurable;
* the existence of a **σ-finite measure `ν` on the group whose null sets are stable under
  right translation**, `ν(B) = 0 ⟹ ν(Bg) = 0`.

Then every measurable almost-invariant function agrees, off a null set for the σ-finite
reference measure to which "almost" refers, with a genuinely invariant function. The
mechanism is a Fubini argument on the product of sample space and group followed by
averaging over the group: the average `ψ(x) = ∫ φ(g·x) dν(g)` is invariant on the
(invariant) set where it is defined, and equals `φ` off a null set.

The right-translation condition holds in particular for a **right-invariant** measure,
whose existence is guaranteed for a large class of groups by Haar theory, but the weaker
null-set form is what the proof needs and is often easy to check directly.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.5
(Almost Invariance), Theorem 6.5.1 (conditions under which an almost invariant test is
equivalent to an invariant one) and Corollary 6.5.1. (`TSH4 §6.5 Thm 6.5.1, Cor 6.5.1`.)

**Main results.**
* `exists_invariant_ae_eq_of_almostInvariant` — almost invariant ⟹ equal a.e. to invariant;
* `IsUMPAlmostInvariant` — UMP within the class of almost-invariant tests;
* `isUMPAlmostInvariant_of_isUMPInvariant` — a UMP invariant test is UMP among almost
  invariant tests.

**Proof formalization notes.**
* The joint-measurability condition is carried by `[MeasurableSMul₂ G 𝓧]`, which asserts
  measurability of `(g, x) ↦ g·x` on the product. This is the same content as the
  product-measurability of `{(x, g) : g·x ∈ A}` for every measurable `A`, up to the swap
  of factors.
* The right-translation null condition is written with preimages, `B·g = (· * g⁻¹) ⁻¹' B`,
  so that measurability of the translate is automatic; `MeasurableMul G` makes the
  translation map measurable.
* The conclusion is an a.e. statement **for the σ-finite measure `μ` to which almost
  invariance refers**, matching the source: the exceptional set is `μ`-null. The reading
  "null for the whole family `P`" is recovered by taking `μ` equivalent to the family,
  which is how the corollary below is set up.
* Non-degeneracy `ν ≠ 0` is stated explicitly. The averaging step normalizes `ν` to a
  probability measure, which is impossible for the zero measure; the source leaves this
  implicit in "there exists a σ-finite measure `ν` over `G`".
* Almost invariance in `IsUMPAlmostInvariant` is taken with respect to **every** member of
  the family (the classical "a.e. `P`" reading), rather than with respect to a single
  dominating measure.

**Bibliographic comments.** The equivalence of almost invariance and invariance under a
group carrying a measure with right-translation-invariant null sets belongs to the circle
of ideas of G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses,"
unpublished manuscript, 1946) and C. Stein ("Some problems in multivariate analysis, Part
I," Technical Report 6, Department of Statistics, Stanford University, 1956); it is used
throughout E. L. Lehmann's development of invariance in the 1950s to compare invariance
with unbiasedness. Counterexamples delimiting the structural hypotheses, and further
results on the relation between the two notions, are due to R. H. Berk and P. J. Bickel
("On invariance and almost invariance," *Ann. Math. Statist.* **39** (1968), 1573–1576)
and R. H. Berk ("A remark on almost invariance," *Ann. Math. Statist.* **41** (1970),
733–735).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧]

/-! ## Almost invariant functions are equivalent to invariant ones -/

/-- **Almost invariant ⟹ equivalent to invariant.** Under joint measurability of the
action and the existence of a nonzero σ-finite measure on the group whose null sets are
stable under right translation, every measurable almost-invariant function coincides, off
a `μ`-null set, with a measurable invariant function. -/
theorem exists_invariant_ae_eq_of_almostInvariant [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓧] {μ : Measure 𝓧} [SigmaFinite μ] {ν : Measure G} [SigmaFinite ν]
    {φ : 𝓧 → ℝ}
    -- USER-INPUT: the group carries a nonzero σ-finite measure
    (hν0 : ν ≠ 0)
    -- USER-INPUT: null sets of `ν` are stable under right translation, `ν B = 0 → ν (B·g) = 0`
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `φ` is measurable
    (hφmeas : Measurable φ)
    -- USER-INPUT: `φ` is almost invariant with respect to `μ`
    (hφ : IsAlmostInvariant G μ φ) :
    ∃ ψ : 𝓧 → ℝ, Measurable ψ ∧ IsInvariantTest G ψ ∧ φ =ᵐ[μ] ψ := by
  -- TODO (Hunt–Stein averaging, not yet formalized). Argument (TSH4 §6.5 Thm 6.5.1): joint
  -- measurability `[MeasurableSMul₂ G 𝓧]` + Fubini on `𝓧 × G` turn the per-`g` a.e. identity
  -- `φ (g • ·) =ᵐ[μ] φ` (`hφ`) into: for `μ`-a.e. `x`, `φ (g • x) = φ x` for `ν`-a.e. `g`.
  -- The invariant representative is the group average `ψ x := ∫ g, φ (g • x) ∂ν̄` for the
  -- normalized `ν̄`; `hν` (right-translation-stable null sets) makes `ψ (g • x) = ψ x` and
  -- `ψ =ᵐ[μ] φ`. Missing Mathlib pieces: (a) the normalization step needs `ν` FINITE (only
  -- `SigmaFinite ν` + `hν0` are given — a σ-finite `ν` is not directly normalizable to a
  -- probability measure, so the averaging integral requires either finiteness or an
  -- invariant-mean / amenability device absent from Mathlib v4.29.1); (b) the quasi-invariance
  -- Fubini transfer of the a.e. identity along right translation. Statement is TRUE for the
  -- intended (Haar-carrying, amenable) groups. No false hypothesis.
  sorry

/-! ## UMP almost invariant tests -/

/-- **UMP almost invariant level-`α` test**: a critical function that is almost invariant
under every member of the family, has level `α`, and dominates on the alternative every
almost-invariant level-`α` competitor. -/
def IsUMPAlmostInvariant (G : Type*) [Group G] [MulAction G 𝓧] (P : Θ → Measure 𝓧)
    (Θ₀ Θ₁ : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsCriticalFn φ ∧ (∀ θ, IsAlmostInvariant G (P θ) φ) ∧ IsLevel P Θ₀ φ α ∧
    ∀ ψ, IsCriticalFn ψ → (∀ θ, IsAlmostInvariant G (P θ) ψ) → IsLevel P Θ₀ ψ α →
      ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ θ

/-- **A UMP invariant test is UMP among almost invariant tests.** Under the structural
assumptions above, together with a σ-finite dominating measure equivalent to the family,
every almost-invariant competitor has the power function of an invariant test, so it
cannot beat a UMP invariant one. -/
theorem isUMPAlmostInvariant_of_isUMPInvariant [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSMul₂ G 𝓧] [MulAction G Θ] {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} [SigmaFinite μ] {ν : Measure G}
    [SigmaFinite ν] {Θ₀ Θ₁ : Set Θ} {α : ℝ} {φ₀ : 𝓧 → ℝ}
    -- USER-INPUT: the group carries a nonzero σ-finite measure with right-translation
    -- stable null sets
    (hν0 : ν ≠ 0)
    (hν : ∀ (g : G) (B : Set G), MeasurableSet B → ν B = 0 →
      ν ((fun y => y * g⁻¹) ⁻¹' B) = 0)
    -- USER-INPUT: `μ` is equivalent to the family: every member is `μ`-absolutely
    -- continuous, and a set null under every member is `μ`-null
    (hdom : ∀ θ, P θ ≪ μ)
    (hequiv : ∀ A : Set 𝓧, MeasurableSet A → (∀ θ, P θ A = 0) → μ A = 0)
    -- USER-INPUT: `φ₀` is UMP among invariant level-`α` tests
    (hφ₀ : IsUMPInvariant G P Θ₀ Θ₁ α φ₀) :
    IsUMPAlmostInvariant G P Θ₀ Θ₁ α φ₀ := by
  -- TODO (depends on `exists_invariant_ae_eq_of_almostInvariant` above, Hunt–Stein). Argument:
  -- a critical almost-invariant level-`α` competitor `ψ` is, by the averaging theorem above,
  -- `=ᵐ[μ]` a genuinely invariant `ψ'`; `hdom`/`hequiv` make the family-a.e. and `μ`-a.e.
  -- readings agree, so `ψ` and `ψ'` share every power `power P · θ`. `ψ'` is then an invariant
  -- level-`α` competitor, so `hφ₀`'s UMP-invariant clause gives `power P ψ θ ≤ power P φ₀ θ` on
  -- `Θ₁`, which is exactly the UMP-almost-invariant domination for `φ₀`. Blocked because the
  -- averaging step `exists_invariant_ae_eq_of_almostInvariant` is itself the lifted Hunt–Stein
  -- gap (see its TODO). Statement is TRUE for the intended amenable groups. No false hypothesis.
  sorry

end StatLean.HypothesisTesting
