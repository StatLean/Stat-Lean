import StatLean.Bayesian.ModelChoice.Defs

/-!
# Credible sets — basic properties

Basic calculus of `γ`-credible set families (`IsCredibleSet post m C γ`: posterior mass of `C x`
is at least `1 − γ`, a.e. data): monotonicity in the level and in the sets, and the trivial
full-space family.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §5.5.1, Definition 5.5.2 (α-credible sets and HPD regions),
p. 260; Example 5.5.3 (normal credible intervals), p. 260.

**Proof formalization notes.** All three lemmas are one-line filter/order arguments
(`tsub_le_tsub_left` for the level, `measure_mono` for the sets, `measure_univ` for the trivial
family — the last needs the posterior values to be probability measures, e.g. any Markov `post`).
The decision-theoretic refinement (HPD regions minimize volume at fixed credibility, Robert
§5.5.3/eq. (5.5.2)) is a Batch-3 target recorded in `notes/bayesian/roadmap.md`.

**Bibliographic comments.** Credible regions are the Bayesian counterpart of Neyman's confidence
sets; the highest-posterior-density convention is systematized in G. E. P. Box and G. C. Tiao,
*Bayesian Inference in Statistical Analysis* (Addison-Wesley, 1973). Robert Definition 5.5.2 and
his §5.5 discussion (including the decision-theoretic loss (5.5.2)) are the account followed
here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  {post : Kernel 𝓧 Θ} {m : Measure 𝓧} {C D : 𝓧 → Set Θ} {γ γ' : ℝ≥0∞}

/-- A `γ`-credible family is `γ'`-credible for any looser level `γ ≤ γ'`. -/
theorem IsCredibleSet.mono_level (h : IsCredibleSet post m C γ)
    -- USER-INPUT: the target level is looser; Robert Definition 5.5.2
    (hγ : γ ≤ γ') :
    IsCredibleSet post m C γ' := by
  filter_upwards [h] with x hx
  exact le_trans (tsub_le_tsub_left hγ 1) hx

/-- Enlarging the sets preserves credibility. -/
theorem IsCredibleSet.mono_set (h : IsCredibleSet post m C γ)
    -- USER-INPUT: pointwise enlargement of the credible sets; Robert Definition 5.5.2
    (hCD : ∀ x, C x ⊆ D x) :
    IsCredibleSet post m D γ := by
  filter_upwards [h] with x hx
  exact le_trans hx (measure_mono (hCD x))

/-- The full-space family is `γ`-credible at every level (for a Markov posterior kernel). -/
theorem isCredibleSet_univ [IsMarkovKernel post] (γ : ℝ≥0∞) :
    IsCredibleSet post m (fun _ => Set.univ) γ := by
  refine ae_of_all m fun x => ?_
  rw [measure_univ]
  exact tsub_le_self

end StatLean.Bayesian
