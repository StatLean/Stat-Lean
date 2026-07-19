import StatLean.HypothesisTesting.Invariance.AlmostInvariance

/-!
# Unbiasedness and invariance coincide when the unbiased solution is unique

Unbiasedness and invariance are logically independent optimality restrictions: each
succeeds on problems where the other does not. Where both deliver a uniformly most
powerful member, however, the two answers agree — and this is not accidental.

The reason is a symmetry of the unbiased class itself. If the testing problem is invariant
under `G`, then a critical function is unbiased of level `α` exactly when its translate
`x ↦ φ(g·x)` is, because translation permutes the null and alternative classes through the
induced action. Hence if `φ*` is UMP unbiased, so is every translate of it, and all of them
have the same power function. If the UMP unbiased test is **unique up to null sets**, all
these translates collapse onto `φ*`, which therefore is almost invariant. A UMP almost
invariant test `φ` is then at least as powerful as `φ*`; conversely `φ` is itself unbiased
(compare it with the invariant constant test `x ↦ α`), so it is dominated by `φ*`. The two
power functions agree, and uniqueness of `φ*` forces `φ = φ*` almost everywhere — which in
passing also makes the UMP almost invariant test unique.

**Main result.** `umpu_eq_umpAlmostInvariant_ae` — with an explicit a.e.-uniqueness
hypothesis on the UMP unbiased test, a UMP unbiased test and a UMP almost invariant test
coincide almost everywhere, and the latter is itself a.e. unique.

**Proof formalization notes.**
* The uniqueness of the unbiased solution is an **explicit hypothesis** (`huniq`), exactly
  as in the source, which assumes "there exists a UMP unbiased test `φ*` which is unique
  up to sets of measure zero". It is stated as: every UMP unbiased level-`α` test agrees
  with `φ*` off a `μ`-null set.
* `μ` is a σ-finite measure equivalent to the family, the standard carrier of "a.e." for
  a dominated model; the equivalence is what lets power equality be converted into a.e.
  equality of tests and back.
* `0 ≤ α ≤ 1` is required because the argument compares the candidate against the constant
  test `x ↦ α`, which must itself be a critical function.
* Stability of the null and alternative classes under the induced action is what makes the
  unbiased class translation-stable; it is stated separately from model invariance.

**Bibliographic comments.** Unbiasedness for tests was introduced by J. Neyman and
E. S. Pearson ("Contributions to the theory of testing statistical hypotheses," *Stat.
Res. Mem.* **1** (1936), 1–37). The consistency of the unbiasedness and (almost)
invariance principles, in the form proved here, belongs to E. L. Lehmann's development of
invariance in the 1950s, resting on the Hunt–Stein circle of ideas (G. A. Hunt and
C. Stein, "Most stringent tests of statistical hypotheses," unpublished manuscript, 1946;
C. Stein, "Some problems in multivariate analysis, Part I," Technical Report 6, Department
of Statistics, Stanford University, 1956). Uniqueness of the unbiased solution, in the
exponential-family setting where it is typically verified, comes from the completeness
theory of E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased
estimation," *Sankhyā* **10** (1950), 305–340).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel)

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] [MulAction G Θ]

/-- **A UMP unbiased test and a UMP almost invariant test coincide a.e.** Given an
invariant testing problem, a σ-finite measure equivalent to the family, and an explicit
a.e.-uniqueness hypothesis on the UMP unbiased test, the UMP almost invariant test equals
the UMP unbiased test off a null set — and is itself unique up to null sets. -/
theorem umpu_eq_umpAlmostInvariant_ae {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {Θ₀ Θ₁ : Set Θ} {α : ℝ} {φstar φ : 𝓧 → ℝ}
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the null and alternative classes are preserved by the induced action
    (hΘ₀ : ∀ (g : G) (θ : Θ), θ ∈ Θ₀ → g • θ ∈ Θ₀)
    (hΘ₁ : ∀ (g : G) (θ : Θ), θ ∈ Θ₁ → g • θ ∈ Θ₁)
    -- USER-INPUT: `μ` is equivalent to the family: every member is `μ`-absolutely
    -- continuous, and a set null under every member is `μ`-null
    (hdom : ∀ θ, P θ ≪ μ)
    (hequiv : ∀ A : Set 𝓧, MeasurableSet A → (∀ θ, P θ A = 0) → μ A = 0)
    -- USER-INPUT: the prescribed level is a probability, so the constant test `x ↦ α`
    -- is an admissible (invariant) competitor
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    -- USER-INPUT: `φstar` is UMP unbiased at level `α`
    (hstar : IsUMPU P Θ₀ Θ₁ α φstar)
    -- USER-INPUT: the UMP unbiased test is unique up to sets of measure zero
    (huniq : ∀ ψ : 𝓧 → ℝ, IsUMPU P Θ₀ Θ₁ α ψ → ψ =ᵐ[μ] φstar)
    -- USER-INPUT: `φ` is UMP among almost invariant level-`α` tests
    (hφ : IsUMPAlmostInvariant G P Θ₀ Θ₁ α φ) :
    φ =ᵐ[μ] φstar ∧ ∀ ψ : 𝓧 → ℝ, IsUMPAlmostInvariant G P Θ₀ Θ₁ α ψ → ψ =ᵐ[μ] φ := by
  sorry

end StatLean.HypothesisTesting
