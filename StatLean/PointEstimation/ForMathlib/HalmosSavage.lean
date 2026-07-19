import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The equivalent countable mixture of a dominated family

The measure-theoretic lemma underlying every treatment of sufficiency for dominated families:
if a family `P : Θ → Measure 𝓧` of probability measures is dominated by a σ-finite `μ`, then
some **countable** mixture `λ = ∑ᵢ cᵢ · P_{θᵢ}` of members of the family is already
*equivalent* to the whole family — every `P θ` is absolutely continuous with respect to `λ`,
and a set is `λ`-null exactly when it is `P θ`-null for every `θ`.

The point is that `λ` is built **from the family itself**, so a `λ`-density is automatically a
legitimate statistical object; densities against an arbitrary dominating `μ` are not. Every
later step — the factorization criterion, minimal sufficiency, the likelihood-ratio
construction — is run against this `λ`.

* `exists_equivalent_countable_mixture` — the existence statement.

**Reference.** Classical theory of dominated families; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* **Route.** Reduce to a finite dominating measure (`μ` σ-finite admits an equivalent finite
  measure). Consider the collection of all countable mixtures `ν` of members of the family,
  and their densities `dν/dμ`; take a sequence `νₙ` whose supports `{dνₙ/dμ > 0}` have
  `μ`-measure converging to the supremum of that quantity over the collection, and let `λ` be
  a strictly positive countable mixture of the `νₙ`. Maximality of the support of `dλ/dμ`
  forces `P θ ≪ λ` for every `θ`: otherwise `P θ` would charge a `λ`-null set and the mixture
  `(λ + P θ)/2` would have strictly larger support, contradicting the supremum.
* **Weights.** `c : ℕ → ℝ≥0∞` is required strictly positive and to sum to `1`, so `λ` is a
  probability measure; the index type is `ℕ` throughout, and `[Nonempty Θ]` lets a genuinely
  finite selection be padded by repetition (repeating an index only merges into a larger
  weight for the same member, which changes neither the null sets nor absolute continuity).
* **The null-set equivalence is stated for an ARBITRARY set `A`,** with no `MeasurableSet`
  hypothesis. This is safe *and* strictly stronger at this pin: `Measure.sum_apply_eq_zero`
  holds for a countable index without measurability, and `Measure.AbsolutelyContinuous` is
  itself defined by an implication between outer-measure values of arbitrary sets. Callers
  that only have a measurable set lose nothing.
* Domination is phrased as `∀ θ, P θ ≪ μ` with `μ` an explicit σ-finite argument rather than
  packaged into a structure, so that the lemma applies verbatim to families dominated by a
  measure produced elsewhere in a proof.

**Bibliographic comments.** The lemma and the equivalent-mixture device are due to
P. R. Halmos and L. J. Savage ("Application of the Radon–Nikodym theorem to the theory of
sufficient statistics," *Ann. Math. Statist.* **20** (1949), 225–241), where they are used to
prove the factorization criterion for dominated families.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-- **Halmos–Savage equivalent-mixture lemma.** A family of probability measures dominated by
a σ-finite measure admits an equivalent countable mixture of its own members: there are
indices `θs : ℕ → Θ` and strictly positive weights `c` summing to `1` such that the mixture
`λ = ∑ᵢ cᵢ · P (θs i)` dominates every member of the family and has exactly the common null
sets of the family. -/
theorem exists_equivalent_countable_mixture {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]
    -- LEAN-ONLY: the index type is inhabited; needed to pad a finite selection by repetition
    -- into a genuine `ℕ`-indexed sequence. No scope change: an empty family is vacuous.
    [Nonempty Θ]
    -- USER-INPUT: the statistical model; genuine external data
    (P : Θ → Measure 𝓧)
    -- USER-INPUT: each member is a probability measure; part of "statistical model"
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: a dominating measure; free choice of reference measure
    (μ : Measure 𝓧)
    -- USER-INPUT: σ-finiteness of the reference measure; the standing regularity of the
    -- dominated-family setting, and false without it (the lemma fails for wild `μ`)
    [SigmaFinite μ]
    -- USER-INPUT: the family is dominated by `μ`; the definition of "dominated family"
    (hdom : ∀ θ, P θ ≪ μ) :
    ∃ (θs : ℕ → Θ) (c : ℕ → ℝ≥0∞) (lam : Measure 𝓧),
      lam = Measure.sum (fun i => c i • P (θs i)) ∧
      (∀ i, 0 < c i) ∧ (∑' i, c i) = 1 ∧
      (∀ θ, P θ ≪ lam) ∧
      ∀ A : Set 𝓧, (∀ θ, P θ A = 0) ↔ lam A = 0 := by
  sorry

end StatLean.PointEstimation
