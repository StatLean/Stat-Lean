import StatLean.HypothesisTesting.NeymanPearson.Lemma

/-!
# Least favorable distributions: reducing a composite hypothesis to a simple one

To test a composite hypothesis `H : {f_θ, θ ∈ ω}` against a simple alternative `g`, replace
`H` by the **simple** hypothesis `H_Λ` whose density is the mixture
$$ h_\Lambda(x) \;=\; \int_\omega f_\theta(x) \, d\Lambda(\theta) $$
over a prior `Λ` carried by `ω`. The fundamental lemma solves the mixed problem. If the
resulting most powerful test happens to keep size `≤ α` against **every** member of `ω`,
then it is most powerful for the original composite problem, and `Λ` is a *least
favorable* prior: no other prior makes the testing problem harder.

Contents:
* `mixtureMeasure μ f Λ` — the mixed hypothesis `H_Λ`;
* `maxPower P₀ G α` — the largest power against `G` available to a level-`α` test of `P₀`;
* `IsLeastFavorable` — `Λ` minimizes that quantity over priors carried by `ω`;
* `isMostPowerful_composite_of_leastFavorable` — the mixed-problem optimum solves the
  composite problem;
* `unique_mostPowerful_composite_of_leastFavorable` — the same transfer for uniqueness;
* `leastFavorable_max_power` — such a `Λ` is least favorable;
* `isMostPowerful_composite_of_npShape` — the practical sufficient condition: a
  likelihood-ratio test against the mixture, whose power is constant `= α` on a
  `Λ`-carrier `ω' ⊆ ω` and `≤ α` on all of `ω`, is most powerful.

**Proof formalization notes.**
* The prior is carried as a measure `Λ : Measure Θ` on the parameter space together with
  `Λ ω = 1`, rather than as a measure on the subtype `ω`. This keeps `power P φ θ` and
  `IsLevel P ω φ α` usable verbatim, and makes "`Λ'` ranges over priors over `ω`" a plain
  side condition rather than a change of ambient type.
* Joint measurability of `(θ, x) ↦ f_θ(x)` is a genuine external input: it is what makes
  `h_Λ` measurable and lets Fubini give `∫ h_Λ dμ = 1`, i.e. that the mixture really is a
  probability density. It cannot be derived from measurability in `x` for each fixed `θ`.
* `maxPower` is a supremum of real numbers over a nonempty set bounded by `1` whenever
  `0 ≤ α`; for `α < 0` the competitor set is empty and the junk value is `0` (Mathlib's
  `sSup ∅`). The theorems below all carry `0 ≤ α`.
* Uniqueness is rendered as `μ`-a.e. equality of critical functions, which is the only
  sense in which a test is ever determined.
* The sufficient condition transcribes the printed pair of conditions faithfully: power
  exactly `α` at every point of the carrier `ω'`, and power at most `α` everywhere on `ω`
  (together these say the supremum over `ω` is attained and equals `α`, since `Λ ω' = 1`
  forces `ω'` to be nonempty).

**Bibliographic comments.** Reducing a composite hypothesis by averaging its members
against a weight function goes back to A. Wald ("Tests of statistical hypotheses
concerning several parameters when the number of observations is large," *Trans. Amer.
Math. Soc.* **54** (1943), 426–482), and the notion of a least favorable prior is central
to A. Wald, *Statistical Decision Functions* (Wiley, 1950). The existence theory and the
transfer results formalized here are due to E. L. Lehmann ("On the existence of least
favorable distributions," *Ann. Math. Statist.* **23** (1952), 408–416); the underlying
optimality of the likelihood-ratio test is J. Neyman and E. S. Pearson (*Phil. Trans. R.
Soc. Lond. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- The **mixed hypothesis** `H_Λ`: the measure whose density with respect to `μ` is the
mixture `h_Λ(x) = ∫ f_θ(x) dΛ(θ)` of the family against the prior. When the inner integral
fails to converge the Bochner integral returns `0` (Mathlib's junk convention); the
theorems below carry the joint-measurability hypothesis that rules this out.

The mixture density is written inline rather than named, because the same notion is already
introduced elsewhere in this area under the name `mixtureDensity`; the two should be
unified into a single shared declaration. -/
noncomputable def mixtureMeasure (μ : Measure 𝓧) (f : Θ → 𝓧 → ℝ) (Λ : Measure Θ) :
    Measure 𝓧 :=
  μ.withDensity fun x => ENNReal.ofReal (∫ θ, f θ x ∂Λ)

/-- The **maximum attainable power** against `G` among level-`α` tests of the simple
hypothesis `P₀`. For `0 ≤ α` the competitor set contains the constant test `φ ≡ α` and is
bounded above by `1`, so this is a genuine supremum; for `α < 0` the set is empty and the
value is the junk `sSup ∅ = 0`. -/
noncomputable def maxPower (P₀ G : Measure 𝓧) (α : ℝ) : ℝ :=
  sSup {b | ∃ φ, IsCriticalFn φ ∧ powerAgainst P₀ φ ≤ α ∧ powerAgainst G φ = b}

/-- `Λ` is **least favorable** at level `α` for testing the family `f` over `ω` against
`G`: no prior carried by `ω` makes less power available to a level-`α` test. -/
def IsLeastFavorable (μ : Measure 𝓧) (f : Θ → 𝓧 → ℝ) (G : Measure 𝓧) (ω : Set Θ)
    (α : ℝ) (Λ : Measure Θ) : Prop :=
  ∀ Λ' : Measure Θ, IsProbabilityMeasure Λ' → Λ' ω = 1 →
    maxPower (mixtureMeasure μ f Λ) G α ≤ maxPower (mixtureMeasure μ f Λ') G α

/-- **Transfer of optimality.** If a most powerful level-`α` test of the mixed hypothesis
`H_Λ` against `g` happens to have size at most `α` against every member of the composite
hypothesis, then it is most powerful for the composite problem itself. -/
theorem isMostPowerful_composite_of_leastFavorable
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null, given as probability measures
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: their densities with respect to `μ`
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of `(θ, x) ↦ f_θ(x)` — what makes the mixture a
    -- density; not implied by measurability in `x` at each fixed `θ`
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set
    (ω : Set Θ)
    -- USER-INPUT: the prior, a probability measure carried by `ω`
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    -- USER-INPUT: nonnegative level
    {α : ℝ} (hα : 0 ≤ α) {φ : 𝓧 → ℝ}
    -- USER-INPUT: `φ` is most powerful for the *mixed* problem
    (hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ)
    -- USER-INPUT: and it keeps level `α` against every member of the composite null —
    -- the hypothesis that makes the whole device work
    (hlevel : IsLevel P ω φ α) :
    IsCriticalFn φ ∧ IsLevel P ω φ α ∧
      ∀ ψ, IsCriticalFn ψ → IsLevel P ω ψ α → powerAgainst G ψ ≤ powerAgainst G φ := by
  -- TODO: needs the mixture-Fubini bridge
  --   `powerAgainst (mixtureMeasure μ f Λ) ψ = ∫ θ, power P ψ θ ∂Λ`
  -- (joint measurability + `integral_integral_swap`); the transfer logic on top is short.
  sorry

/-- **Transfer of uniqueness.** Under the hypotheses above, if the mixed problem has an
essentially unique most powerful level-`α` test, then so does the composite problem, with
the same solution. -/
theorem unique_mostPowerful_composite_of_leastFavorable
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null and its densities
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of the family
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set and the prior carried by it
    (ω : Set Θ) (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    -- USER-INPUT: nonnegative level
    {α : ℝ} (hα : 0 ≤ α) {φ : 𝓧 → ℝ}
    -- USER-INPUT: `φ` is most powerful for the mixed problem, and keeps level on `ω`
    (hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ)
    (hlevel : IsLevel P ω φ α)
    -- USER-INPUT: essential uniqueness for the mixed problem — the printed hypothesis
    (huniq : ∀ ψ, IsMostPowerful (mixtureMeasure μ f Λ) G α ψ → ψ =ᵐ[μ] φ) :
    ∀ ψ, IsCriticalFn ψ → IsLevel P ω ψ α →
      (∀ χ, IsCriticalFn χ → IsLevel P ω χ α → powerAgainst G χ ≤ powerAgainst G ψ) →
      ψ =ᵐ[μ] φ := by
  -- TODO: needs the mixture-Fubini bridge
  --   `powerAgainst (mixtureMeasure μ f Λ) ψ = ∫ θ, power P ψ θ ∂Λ`
  -- (joint measurability + `integral_integral_swap`); the transfer logic on top is short.
  sorry

/-- **The prior is least favorable.** A prior whose mixed-problem optimum keeps level `α`
against the whole composite null minimizes the power available against the alternative. -/
theorem leastFavorable_max_power
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null and its densities
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of the family
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set and the prior carried by it
    (ω : Set Θ) (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω = 1)
    -- USER-INPUT: nonnegative level
    {α : ℝ} (hα : 0 ≤ α) {φ : 𝓧 → ℝ}
    -- USER-INPUT: `φ` is most powerful for the mixed problem, and keeps level on `ω`
    (hMP : IsMostPowerful (mixtureMeasure μ f Λ) G α φ)
    (hlevel : IsLevel P ω φ α) :
    IsLeastFavorable μ f G ω α Λ := by
  -- TODO: needs the mixture-Fubini bridge
  --   `powerAgainst (mixtureMeasure μ f Λ) ψ = ∫ θ, power P ψ θ ∂Λ`
  -- (joint measurability + `integral_integral_swap`); the transfer logic on top is short.
  sorry

/-- **The practical sufficient condition.** Let `Λ` be a prior carried by a subset
`ω' ⊆ ω` with `Λ ω' = 1`, and let `φ` be a likelihood-ratio test of the mixture density
against `g` at some threshold `k`. If the power of `φ` is exactly `α` at every point of
`ω'` and at most `α` on all of `ω`, then `φ` is most powerful at level `α` for the
composite problem. -/
theorem isMostPowerful_composite_of_npShape
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the family under the null and its densities
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → 𝓧 → ℝ) (hf : ∀ θ, HasDensity μ (f θ) (P θ))
    -- USER-INPUT: joint measurability of the family
    (hjoint : Measurable fun q : Θ × 𝓧 => f q.1 q.2)
    -- USER-INPUT: the simple alternative and its density
    (G : Measure 𝓧) [IsProbabilityMeasure G] (g : 𝓧 → ℝ) (hg : HasDensity μ g G)
    -- USER-INPUT: the null parameter set, and a `Λ`-carrier inside it
    (ω ω' : Set Θ) (hω' : ω' ⊆ ω)
    -- USER-INPUT: the prior, carried by `ω'`
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] (hΛ : Λ ω' = 1)
    -- USER-INPUT: nonnegative level, threshold, and the candidate test
    {α : ℝ} (hα : 0 ≤ α) {k : ℝ≥0∞} {φ : 𝓧 → ℝ} (hφ : IsCriticalFn φ)
    -- USER-INPUT: `φ` is a likelihood-ratio test of the mixture against the alternative
    (hshape : HasNPShape μ (fun x => ∫ θ, f θ x ∂Λ) g k φ)
    -- USER-INPUT: its power is exactly `α` on the carrier — first half of the printed
    -- condition; together with `Λ ω' = 1` this forces `ω'` to be nonempty
    (hsize : ∀ θ ∈ ω', power P φ θ = α)
    -- USER-INPUT: and at most `α` on the whole null — second half (the supremum over `ω`
    -- is attained on `ω'` and equals `α`)
    (hlevel : IsLevel P ω φ α) :
    IsCriticalFn φ ∧ IsLevel P ω φ α ∧
      ∀ ψ, IsCriticalFn ψ → IsLevel P ω ψ α → powerAgainst G ψ ≤ powerAgainst G φ := by
  -- TODO: needs the mixture-Fubini bridge
  --   `powerAgainst (mixtureMeasure μ f Λ) ψ = ∫ θ, power P ψ θ ∂Λ`
  -- (joint measurability + `integral_integral_swap`); the transfer logic on top is short.
  sorry

end StatLean.HypothesisTesting
