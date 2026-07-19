import StatLean.PointEstimation.Completeness.Defs
import StatLean.PointEstimation.Sufficiency.Defs
import Mathlib.Probability.Independence.Basic

/-!
# Independence of a complete sufficient statistic from an ancillary statistic

If `T` is a boundedly complete sufficient statistic for a family of probability measures and
`V` is ancillary — its law does not depend on the parameter — then `T` and `V` are
independent under every member of the family. The argument is short and is the reason
completeness is the right strengthening of sufficiency: for a measurable set `A`, the
conditional probability `η_A(t) = P(V ∈ A ∣ T = t)` is parameter-free by sufficiency, its
mean `E_θ[η_A(T)] = P_θ(V ∈ A)` is parameter-free by ancillarity, and completeness applied to
`η_A − P(V ∈ A)` — a function bounded by `1` — forces `η_A` to be constant almost everywhere.
Constancy of the conditional probability is exactly independence.

* `IsCompleteFamily.boundedlyComplete` / `completeStat_boundedlyCompleteStat` — completeness
  implies bounded completeness for families of probability measures;
* `indepFun_of_boundedlyComplete_sufficient` — the independence theorem.

**Reference.** Classical completeness and ancillarity theory; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* The theorem is stated with **bounded** completeness, which is all the proof consumes: the
  test function `η_A − P(V ∈ A)` is bounded by `1`. Stating it this way makes it strictly
  more applicable than the version assuming full completeness, and
  `completeStat_boundedlyCompleteStat` bridges the two whenever a caller has the stronger
  hypothesis.
* Sufficiency is taken in the kernel (graph/compProd) form. That form is what delivers the
  single θ-free determination `η_A(t) = Q t (V ⁻¹' A)` of the conditional probability
  simultaneously for all `A`, together with the fibre property that makes
  `E_θ[η_A(T)] = P_θ(V ∈ A)` a plain disintegration identity rather than an a.e. juggling
  argument.
* Both statistics are required measurable; `T` because the completeness hypothesis is about
  the family of its laws, and `V` because `Q t (V ⁻¹' A)` must be a measurable function of
  `t`. Neither codomain needs any structure beyond a measurable space, so the ancillary
  statistic is allowed to take values in a space different from the sufficient statistic's.
* `completeStat_boundedlyCompleteStat` is the specialization of `IsCompleteFamily.
  boundedlyComplete` to laws of a statistic; measurability of the statistic enters only to
  know that each pushed-forward law is again a probability measure, under which a bounded
  measurable function is automatically integrable.

**Bibliographic comments.** Completeness and its role in unbiased estimation and similar
regions are due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased
estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236). The independence
result proved here is due to D. Basu ("On statistics independent of a complete sufficient
statistic," *Sankhyā* **15** (1955), 377–380).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S S' : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S] [MeasurableSpace S']

/-- For a family of **probability** measures, completeness implies bounded completeness: a
bounded measurable function is integrable against every member. -/
theorem IsCompleteFamily.boundedlyComplete {Q : Θ → Measure S}
    -- LEAN-ONLY: the laws are probability measures, so bounded ⇒ integrable; the implication
    -- fails for infinite measures and the classical statement is always about probabilities
    [∀ θ, IsProbabilityMeasure (Q θ)]
    -- USER-INPUT: completeness of the family
    (h : IsCompleteFamily Q) :
    IsBoundedlyCompleteFamily Q := by
  sorry

/-- Statistic form: a complete statistic of a family of probability measures is boundedly
complete. -/
theorem completeStat_boundedlyCompleteStat {P : Θ → Measure 𝓧} {T : 𝓧 → S}
    -- LEAN-ONLY: the model consists of probability measures; see
    -- `IsCompleteFamily.boundedlyComplete`
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the statistic is measurable
    (hT : Measurable T)
    -- USER-INPUT: completeness of the statistic
    (h : IsCompleteStat P T) :
    IsBoundedlyCompleteStat P T := by
  sorry

/-- **Basu's theorem**: a boundedly complete sufficient statistic is independent of every
ancillary statistic, under every member of the family. -/
theorem indepFun_of_boundedlyComplete_sufficient {P : Θ → Measure 𝓧} {T : 𝓧 → S} {V : 𝓧 → S'}
    -- LEAN-ONLY: the model consists of probability measures; independence is a statement
    -- about probabilities and the disintegration argument needs total mass one
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the sufficient statistic is measurable
    (hT : Measurable T)
    -- USER-INPUT: the ancillary statistic is measurable
    (hV : Measurable V)
    -- USER-INPUT: sufficiency of `T`, in the θ-free Markov-kernel form
    (hsuff : HasSufficientKernel P T)
    -- USER-INPUT: bounded completeness of `T`; the classical hypothesis, and all the proof
    -- uses (the test function is a conditional probability, bounded by one)
    (hcomp : IsBoundedlyCompleteStat P T)
    -- USER-INPUT: ancillarity of `V`: its law does not depend on the parameter
    (hanc : IsAncillary P V) :
    ∀ θ, IndepFun T V (P θ) := by
  sorry

end StatLean.PointEstimation
