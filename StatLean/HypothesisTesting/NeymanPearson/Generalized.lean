import StatLean.HypothesisTesting.NeymanPearson.Lemma
import Mathlib.Analysis.Convex.Basic

/-!
# The generalized fundamental lemma: maximization under several side conditions

Given integrable `f₁, …, f_{m+1}` and constants `c₁, …, c_m`, consider the class `𝒞` of
critical functions `φ` obeying the `m` side conditions
$$ \int \varphi f_i \, d\mu \;=\; c_i, \qquad i = 1, \dots, m, $$
and the problem of maximizing `∫ φ f_{m+1} dμ` over `𝒞`. A maximizer exists as soon as
`𝒞` is nonempty; it is characterized — sufficiently always, necessarily at inner points
of the attainable-moment set — by the undetermined-multiplier shape
$$ \varphi(x) = 1 \ \text{ when } f_{m+1}(x) > \textstyle\sum_i k_i f_i(x), \qquad
   \varphi(x) = 0 \ \text{ when } f_{m+1}(x) < \textstyle\sum_i k_i f_i(x). $$

Contents:
* `momentSet μ f` — the attainable-moment set `{(∫φf₁dμ, …, ∫φf_mdμ) : φ critical}`;
* `HasMultiplierShape μ f k φ` — the multiplier shape above, `μ`-a.e.;
* `exists_test_max_integral_of_constraints` — existence of a maximizer over `𝒞`;
* `isMax_of_multiplier_form` — sufficiency of the multiplier shape;
* `isMax_le_of_multiplier_form_nonneg` — with `kᵢ ≥ 0`, maximality also against the
  larger class defined by the *inequality* constraints `∫φfᵢdμ ≤ cᵢ`;
* `convex_isClosed_momentSet`, `exists_multipliers_of_max` — the geometry of the moment
  set, and the existence *and* necessity of the multipliers at an inner point;
* `exists_test_with_prescribed_sizes` — a test of prescribed size `α` against `m`
  distributions whose power against the `(m+1)`-st strictly exceeds `α`;
* `isMax_of_lagrangian` — the abstract Lagrangian sufficiency principle behind all of it.

**Proof formalization notes.**
* The classical statement is set on a Euclidean sample space; the only role of that
  assumption is to support the weak compactness theorem for critical functions, which
  holds for a σ-finite dominating measure. We therefore work with a general measurable
  space and `[SigmaFinite μ]`, which is a strict generalization of the printed form.
* The `m` side conditions are indexed by `Fin m` embedded into `Fin (m+1)` via
  `Fin.castSucc`, and the objective is the last coordinate `Fin.last m`. This keeps a
  single function family `f : Fin (m+1) → 𝓧 → ℝ` rather than a pair.
* `HasMultiplierShape` is stated `μ`-a.e. rather than pointwise. This makes the
  sufficiency statements strictly stronger than the printed pointwise form, and makes the
  necessity statement land exactly on the printed conclusion ("(3.30) holds a.e. μ").
* `exists_multipliers_of_max` bundles both halves of the inner-point clause under a
  single `∃ k`: the multipliers exhibited by the supporting hyperplane are the same ones
  that every maximizer is forced to use. Splitting them would silently weaken the result.
* The inner-point hypothesis is transcribed as membership in the ambient `interior` of the
  moment set inside `Fin m → ℝ`. The classical statement is available in two readings:
  ambient interior, or interior relative to the smallest linear space containing the
  moment set. The relative reading is the *weaker hypothesis*, hence the stronger theorem,
  and is the one classically proved. We state only the ambient version here; upgrading to
  the relative-interior hypothesis is a deliberate, documented gap.

**Bibliographic comments.** The extension of the fundamental lemma to several side
conditions is due to J. Neyman and E. S. Pearson ("Contributions to the theory of testing
statistical hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37); its definitive
measure-theoretic form, including the discussion of what happens when the inner-point
condition fails, is due to G. B. Dantzig and A. Wald ("On the fundamental lemma of Neyman
and Pearson," *Ann. Math. Statist.* **22** (1951), 87–93). The use of the resulting
multipliers to construct optimal tests of composite hypotheses is developed in
E. L. Lehmann ("On the existence of least favorable distributions," *Ann. Math. Statist.*
**23** (1952), 408–416).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **attainable-moment set**: the set of vectors `(∫φf₁dμ, …, ∫φf_mdμ)` obtained as
`φ` ranges over all critical functions. It is convex and closed (`convex_isClosed_momentSet`),
and the constraint vector being one of its inner points is the hypothesis under which
undetermined multipliers exist. For `m = 0` it is the one-point set `{()}`. -/
def momentSet {m : ℕ} (μ : Measure 𝓧) (f : Fin m → 𝓧 → ℝ) : Set (Fin m → ℝ) :=
  {u | ∃ φ, IsCriticalFn φ ∧ ∀ i, ∫ x, φ x * f i x ∂μ = u i}

/-- The **undetermined-multiplier shape** with multipliers `k`: `φ` rejects `μ`-a.e. where
`f_{m+1} > ∑ kᵢfᵢ` and accepts `μ`-a.e. where `f_{m+1} < ∑ kᵢfᵢ`, with no constraint on
the boundary set `{f_{m+1} = ∑ kᵢfᵢ}`. This is the `m`-constraint analogue of the
likelihood-ratio shape; the pointwise form of the classical statement implies it. -/
def HasMultiplierShape {m : ℕ} (μ : Measure 𝓧) (f : Fin (m + 1) → 𝓧 → ℝ) (k : Fin m → ℝ)
    (φ : 𝓧 → ℝ) : Prop :=
  (∀ᵐ x ∂μ, ∑ i, k i * f i.castSucc x < f (Fin.last m) x → φ x = 1) ∧
    (∀ᵐ x ∂μ, f (Fin.last m) x < ∑ i, k i * f i.castSucc x → φ x = 0)

/-- **Existence (i).** If some critical function satisfies the `m` side conditions, then
one of them maximizes `∫ φ f_{m+1} dμ` over the whole class. -/
theorem exists_test_max_integral_of_constraints {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite (replaces the Euclidean-space assumption)
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    (f : Fin (m + 1) → 𝓧 → ℝ)
    -- USER-INPUT: measurability of the data (needed for the integrals to be meaningful)
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data — the printed hypothesis "integrable μ"
    (hint : ∀ i, Integrable (f i) μ)
    -- USER-INPUT: the prescribed values of the side conditions
    (c : Fin m → ℝ)
    -- USER-INPUT: the constraint class is nonempty (printed as "there exists a critical
    -- function φ satisfying (3.29)"); without it the conclusion is false for `m ≥ 1`
    (hne : ∃ φ, IsCriticalFn φ ∧ ∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) :
    ∃ φ, IsCriticalFn φ ∧ (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) ∧
      ∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ = c i) →
        ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ := by
  sorry

/-- **Sufficiency (ii).** A member of the constraint class that has the multiplier shape
for *some* multipliers `k` maximizes `∫ φ f_{m+1} dμ` over that class. No sign condition
on `k` is needed here. -/
theorem isMax_of_multiplier_form {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    {f : Fin (m + 1) → 𝓧 → ℝ}
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ)
    {c : Fin m → ℝ} {k : Fin m → ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the candidate is a critical function
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the candidate satisfies the side conditions
    (hcon : ∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i)
    -- USER-INPUT: the candidate has the multiplier shape for the given `k`
    (hshape : HasMultiplierShape μ f k φ) :
    ∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ = c i) →
      ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ := by
  sorry

/-- **Sufficiency (iii), nonnegative multipliers.** If the multipliers are nonnegative,
the same test is maximal against the *larger* competitor class defined by the inequality
constraints `∫ψfᵢdμ ≤ cᵢ`. -/
theorem isMax_le_of_multiplier_form_nonneg {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    {f : Fin (m + 1) → 𝓧 → ℝ}
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ)
    {c : Fin m → ℝ} {k : Fin m → ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the candidate is a critical function
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the candidate satisfies the side conditions with equality
    (hcon : ∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i)
    -- USER-INPUT: the multipliers are nonnegative — exactly what upgrades the competitor
    -- class from equality to inequality constraints
    (hk : ∀ i, 0 ≤ k i)
    -- USER-INPUT: the candidate has the multiplier shape for the given `k`
    (hshape : HasMultiplierShape μ f k φ) :
    ∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ ≤ c i) →
      ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ := by
  sorry

/-- **Geometry of the moment set (iv, first clause).** The attainable-moment set is convex
and closed. Convexity is immediate from convexity of the class of critical functions;
closedness is the weak compactness theorem for critical functions. -/
theorem convex_isClosed_momentSet {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the constraint functions
    (f : Fin m → 𝓧 → ℝ)
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ) :
    Convex ℝ (momentSet μ f) ∧ IsClosed (momentSet μ f) := by
  sorry

/-- **Multipliers exist, and are forced (iv, second clause).** If the constraint vector is
an inner point of the attainable-moment set, then there are multipliers `k` such that

* some critical function satisfies the side conditions *and* has the multiplier shape;
* **every** maximizer in the constraint class has that same shape `μ`-a.e.

The two halves share one `∃ k`: the multipliers produced by the supporting hyperplane are
the ones every maximizer must use. -/
theorem exists_multipliers_of_max {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    (f : Fin (m + 1) → 𝓧 → ℝ)
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ)
    {c : Fin m → ℝ}
    -- USER-INPUT: the constraint vector is an *inner point* of the attainable-moment set
    -- (ambient interior in `Fin m → ℝ`); this is the printed hypothesis, and it cannot be
    -- dropped: on the boundary the multiplier characterization genuinely fails
    (hc : c ∈ interior (momentSet μ fun i => f i.castSucc)) :
    ∃ k : Fin m → ℝ,
      (∃ φ, IsCriticalFn φ ∧ (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) ∧
        HasMultiplierShape μ f k φ) ∧
      ∀ φ, IsCriticalFn φ → (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) →
        (∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ = c i) →
          ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ) →
        HasMultiplierShape μ f k φ := by
  sorry

/-- **A test with prescribed sizes.** Given `m + 1` probability densities and a level
`0 < α < 1`, there is a test whose size against each of the first `m` distributions is
exactly `α` and whose power against the last strictly exceeds `α` — unless the last
density is a linear combination of the others almost everywhere, in which case no such
test can exist. -/
theorem exists_test_with_prescribed_sizes {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` distributions, given as probability measures
    (P : Fin (m + 1) → Measure 𝓧) [∀ i, IsProbabilityMeasure (P i)]
    -- USER-INPUT: their densities with respect to `μ`
    (p : Fin (m + 1) → 𝓧 → ℝ) (hp : ∀ i, HasDensity μ (p i) (P i))
    -- USER-INPUT: nondegenerate level; at `α ∈ {0,1}` the strict inequality fails
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (∃ k : Fin m → ℝ, ∀ᵐ x ∂μ, p (Fin.last m) x = ∑ i, k i * p i.castSucc x) ∨
      ∃ φ, IsCriticalFn φ ∧ (∀ i : Fin m, powerAgainst (P i.castSucc) φ = α) ∧
        α < powerAgainst (P (Fin.last m)) φ := by
  sorry

/-- **Lagrangian sufficiency.** Abstract form of the multiplier argument, on an arbitrary
space `U`: a point satisfying the side conditions which maximizes the Lagrangian
`F_{m+1} - ∑ kᵢFᵢ` over *all* of `U`, for some multipliers `k`, maximizes `F_{m+1}` over
the points satisfying the side conditions.

Applied with `U` the class of critical functions and `Fᵢ(φ) = ∫ φ fᵢ dμ`, this is exactly
the sufficiency half of the generalized lemma; in practice one maximizes for arbitrary
`k` and then chooses `k` to meet the side conditions. -/
theorem isMax_of_lagrangian {U : Type*} {m : ℕ}
    -- USER-INPUT: the objective (last index) and the `m` constrained functionals
    (F : Fin (m + 1) → U → ℝ)
    -- USER-INPUT: the prescribed values of the side conditions
    (c : Fin m → ℝ)
    -- USER-INPUT: the multipliers, a free choice
    (k : Fin m → ℝ) {u₀ : U}
    -- USER-INPUT: the candidate satisfies the side conditions
    (hu₀ : ∀ i, F i.castSucc u₀ = c i)
    -- USER-INPUT: the candidate maximizes the Lagrangian over the *whole* space
    (hlag : ∀ u, F (Fin.last m) u - ∑ i, k i * F i.castSucc u ≤
      F (Fin.last m) u₀ - ∑ i, k i * F i.castSucc u₀) :
    ∀ u, (∀ i, F i.castSucc u = c i) → F (Fin.last m) u ≤ F (Fin.last m) u₀ := by
  sorry

end StatLean.HypothesisTesting
