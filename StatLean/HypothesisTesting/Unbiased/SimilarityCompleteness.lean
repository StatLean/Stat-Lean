import StatLean.HypothesisTesting.Tests.Defs
import StatLean.PointEstimation.Sufficiency.Defs
import StatLean.PointEstimation.Completeness.Defs
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

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

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.3 (Similarity and Completeness), Theorem 4.3.2 (similar tests have
Neyman structure iff the sufficient statistic is boundedly complete), together with Theorem
4.3.1 (completeness of the natural statistic of a full-rank family). (`TSH4 §4.3 Thm 4.3.2,
Thm 4.3.1`.)

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
  haveI := hQ
  haveI hstatprob : ∀ θ, IsProbabilityMeasure (statLaw P T θ) := fun θ => by
    rw [statLaw]; exact Measure.isProbabilityMeasure_map hT.aemeasurable
  -- the conditional size `t ↦ ∫ φ dQ_t`, measurable and bounded by `1`
  have hcond_meas : Measurable (fun t => ∫ x, φ x ∂(Q t)) :=
    (StronglyMeasurable.integral_kernel (κ := Q) hφ.1.stronglyMeasurable).measurable
  have hcond_bd : ∀ t, |∫ x, φ x ∂(Q t)| ≤ 1 := fun t => by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, φ x ∂(Q t)‖ ≤ 1 * (Q t Set.univ).toReal :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [(hφ.2 x).1], (hφ.2 x).2⟩)
      _ = 1 := by rw [measure_univ, ENNReal.toReal_one, mul_one]
  have hcond_int : ∀ θ, Integrable (fun t => ∫ x, φ x ∂(Q t)) (statLaw P T θ) := fun θ =>
    Integrable.of_bound hcond_meas.aestronglyMeasurable 1
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hcond_bd t)
  -- the disintegration identity `∫ φ dP_θ = ∫ (∫ φ dQ_t) d(statLaw)`
  have hdis : ∀ θ ∈ ω, ∫ x, φ x ∂(P θ) = ∫ t, (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) := by
    intro θ hθ
    have hfm : Measurable (fun x => (T x, x)) := hT.prodMk measurable_id
    have hgm : Measurable (fun z : 𝓣 × 𝓧 => φ z.2) := hφ.1.comp measurable_snd
    have hint' : Integrable (fun z : 𝓣 × 𝓧 => φ z.2) ((statLaw P T θ) ⊗ₘ Q) :=
      Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hφ.2 z.2).1], (hφ.2 z.2).2⟩)
    calc ∫ x, φ x ∂(P θ)
        = ∫ z, φ z.2 ∂((P θ).map (fun x => (T x, x))) :=
          (integral_map hfm.aemeasurable hgm.aestronglyMeasurable).symm
      _ = ∫ z, φ z.2 ∂((statLaw P T θ) ⊗ₘ Q) := by rw [hsuff θ hθ]
      _ = ∫ t, (∫ x, φ x ∂(Q t)) ∂(statLaw P T θ) := Measure.integral_compProd hint'
  -- the deviation `ψ t = ∫ φ dQ_t − α` integrates to `0` over every boundary law
  set ψ : 𝓣 → ℝ := fun t => (∫ x, φ x ∂(Q t)) - α with hψ_def
  have hψ_meas : Measurable ψ := hcond_meas.sub measurable_const
  have hψ_bdd : ∃ C, ∀ s, |ψ s| ≤ C := ⟨1 + |α|, fun t => by
    have h1 := hcond_bd t
    have h2 : |ψ t| ≤ |∫ x, φ x ∂(Q t)| + |α| := by
      show |(∫ x, φ x ∂(Q t)) - α| ≤ |∫ x, φ x ∂(Q t)| + |α|
      rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans_eq ?_; rw [abs_neg]
    linarith⟩
  have hzero : ∀ θ : ω, ∫ s, ψ s ∂(statLaw P T (θ : Θ)) = 0 := by
    intro θ
    have hθω : (θ : Θ) ∈ ω := θ.2
    simp only [hψ_def]
    rw [integral_sub (hcond_int _) (integrable_const α), integral_const,
      probReal_univ, smul_eq_mul, one_mul, ← hdis (θ : Θ) hθω]
    have hval : ∫ x, φ x ∂(P (θ : Θ)) = α := hsim (θ : Θ) hθω
    rw [hval, sub_self]
  -- bounded completeness forces `ψ = 0` a.e., i.e. conditional size `α`
  have hae := hcomplete ψ hψ_meas hψ_bdd hzero
  intro θ hθ
  filter_upwards [hae ⟨θ, hθ⟩] with t ht
  have : (∫ x, φ x ∂(Q t)) - α = 0 := ht
  linarith

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
  -- TODO: lifted debt of this file. The perturbation `φ = c·(f∘T) + α` (with
  -- `c = min(α,1−α)/M`) is a critical function and is similar (its power is
  -- `c·∫ f d(statLaw) + α = α`), so `hall` gives `∀ᵐ t, ∫ φ dQ_t = α`, i.e.
  -- `∀ᵐ t, c·(∫ f(T x) dQ_t) = 0`, hence `∫ f(T x) dQ_t = 0` a.e. To conclude `f = 0` a.e.
  -- one needs `∫ f(T x) dQ_t = f t` for a.e. `t` — the fibre-support of `Q` from `hsuff`,
  -- `∀ᵐ (t,x) ∂(statLaw ⊗ₘ Q), T x = t`. Establishing that a.e. identity requires the diagonal
  -- `{(t,x) | T x = t}` to be measurable in `𝓣 × 𝓧` (`measurableSet_eq_fun`), which needs a
  -- countably-separated / standard-Borel structure on `𝓣` not present in the signature. Fix =
  -- add `[StandardBorelSpace 𝓣]` (as the point-estimation `Sufficiency.Basic` fibre lemmas do),
  -- then transport the fibre-support along `hsuff`. See the report for the flagged hypothesis gap.
  sorry

end StatLean.HypothesisTesting
