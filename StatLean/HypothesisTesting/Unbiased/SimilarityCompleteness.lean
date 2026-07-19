import StatLean.HypothesisTesting.Tests.Defs
import StatLean.PointEstimation.Sufficiency.Defs
import StatLean.PointEstimation.Completeness.Defs

/-!
# Similar tests have Neyman structure iff the sufficient statistic is boundedly complete

Fix a boundary family `{P_θ : θ ∈ ω}` and a statistic `T` that is sufficient for it, with
θ-free conditional (Markov) kernel `Q`. A test `φ` is **similar** on `ω` when its power is
identically `α` there, and it has **Neyman structure** when its *conditional* size given
`T = t` equals `α`. Neyman structure always implies similarity (average the conditional
size); the converse — every similar test has Neyman structure — holds exactly when the
family of laws of `T` on `ω` is **boundedly complete**:

* `hasNeymanStructure_of_boundedlyComplete` — bounded completeness ⇒ every similar test has
  Neyman structure;
* `boundedlyComplete_of_forall_similar_hasNeymanStructure` — the converse.

This is the engine that reduces optimal similar tests to a family of one-dimensional
conditional Neyman–Pearson problems, one on each surface `T = t`.

**Reference.** Classical theory of similar regions; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* *The almost-everywhere carrier.* The source states both the Neyman-structure condition and
  the completeness conclusion "a.e. `𝒫^T`", meaning: outside one exceptional set that is
  null under **every** member of the family. For a *fixed* function this is literally
  equivalent to the per-parameter form `∀ θ ∈ ω, ∀ᵐ t ∂(statLaw P T θ), …` used below
  (both say that `{t | …}` has measure zero under every `statLaw P T θ`, `θ ∈ ω`), so we
  quantify over every boundary parameter rather than fixing a single dominating reference
  measure `ν`. Instantiating `HasNeymanStructure` at `ν := statLaw P T θ` for each `θ ∈ ω`
  is exactly that reading.
* Sufficiency enters in the graph (`compProd`) form: `(P θ).map (x ↦ (T x, x)) =
  statLaw P T θ ⊗ₘ Q`. Beyond disintegration this pins `Q t` to the fibre `{x | T x = t}`
  for a.e. `t`, which the converse direction needs in order to compute the conditional size
  of a test of the form `c·f(T ·) + α`.
* Sufficiency and bounded completeness are required only on the boundary family, so both
  are stated for the restriction `fun θ : ω => …`; a sufficient statistic for the whole
  model restricts to one for any subfamily, but the converse is false for completeness, and
  the boundary subfamily is the one the applications complete.
* The converse direction needs `0 < α < 1`: the perturbation `φ = c·f(T ·) + α` used to
  contradict bounded completeness is a critical function only for `c ≤ min(α, 1−α)/M`,
  which is positive precisely then.

**Bibliographic comments.** Similar regions and the notion of Neyman structure are due to
J. Neyman ("Sur la vérification des hypothèses statistiques composées," *Bull. Soc. Math.
France* **63** (1935), 246–266; "Outline of a theory of statistical estimation based on the
classical theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380). The
equivalence with (bounded) completeness of the sufficient statistic, and the completeness
concept itself, are due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and
unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236).
-/

open MeasureTheory ProbabilityTheory
open StatLean.PointEstimation

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 𝓣 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓣]

/-- **Bounded completeness ⇒ Neyman structure.**

If the laws of the sufficient statistic `T` over the boundary set `ω` form a boundedly
complete family, then every similar level-`α` test has Neyman structure: its conditional
size given `T = t` equals `α` for almost every `t`, under every boundary parameter.

Proof route: similarity says `∫ (φ − α) dP_θ = 0` for `θ ∈ ω`; disintegrating along `T`
turns this into `∫ ψ d(statLaw P T θ) = 0` for the bounded measurable function
`ψ t = ∫ φ dQ_t − α`; bounded completeness forces `ψ = 0` a.e. -/
theorem hasNeymanStructure_of_boundedlyComplete
    {P : Θ → Measure 𝓧} {ω : Set Θ} {T : 𝓧 → 𝓣} {Q : Kernel 𝓣 𝓧} {α : ℝ} {φ : 𝓧 → ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: `T` is measurable; part of the statistic's data
    (hT : Measurable T)
    -- USER-INPUT: `Q` is a Markov kernel — the θ-free conditional distribution given `T`
    (hQ : IsMarkovKernel Q)
    -- USER-INPUT: `T` is sufficient for the boundary family, in graph (disintegration) form
    (hsuff : ∀ θ ∈ ω, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: the laws of `T` over the boundary set are boundedly complete
    (hcomplete : IsBoundedlyCompleteFamily fun θ : ω => statLaw P T (θ : Θ))
    -- USER-INPUT: `φ` is a randomized test
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: `φ` is similar of size `α` on the boundary set
    (hsim : IsSimilar P ω α φ) :
    ∀ θ ∈ ω, HasNeymanStructure T Q (statLaw P T θ) α φ := by
  sorry

/-- **Neyman structure for all similar tests ⇒ bounded completeness.**

Converse direction. If bounded completeness failed, a bounded `f` with `∫ f d(statLaw) = 0`
for all boundary parameters and `f ≠ 0` with positive probability would yield the similar
test `φ = c·f(T ·) + α` (with `c = min(α, 1−α)/M`, `M` a bound for `|f|`), whose conditional
size is `c·f(t) + α ≠ α` on a non-null set — contradicting the assumed Neyman structure. -/
theorem boundedlyComplete_of_forall_similar_hasNeymanStructure
    {P : Θ → Measure 𝓧} {ω : Set Θ} {T : 𝓧 → 𝓣} {Q : Kernel 𝓣 𝓧} {α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: `T` is measurable; part of the statistic's data
    (hT : Measurable T)
    -- USER-INPUT: `Q` is a Markov kernel — the θ-free conditional distribution given `T`
    (hQ : IsMarkovKernel Q)
    -- USER-INPUT: `T` is sufficient for the boundary family, in graph (disintegration) form
    (hsuff : ∀ θ ∈ ω, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; the perturbing test
    -- `c·f(T ·) + α` is a critical function only then, no scope change (α ∈ {0,1} is
    -- degenerate for testing)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: every similar level-`α` test has Neyman structure with respect to `T`
    (hall : ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsSimilar P ω α φ →
      ∀ θ ∈ ω, HasNeymanStructure T Q (statLaw P T θ) α φ) :
    IsBoundedlyCompleteFamily fun θ : ω => statLaw P T (θ : Θ) := by
  sorry

end StatLean.HypothesisTesting
