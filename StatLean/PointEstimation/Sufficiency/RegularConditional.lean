import StatLean.PointEstimation.Sufficiency.Factorization
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# From per-event determinations to a θ-free regular conditional distribution

The definition of sufficiency only asks that *each* event `A` admit a determination of
`P_θ(A ∣ T = t)` free of `θ`. What decision theory actually uses is stronger: a single θ-free
Markov kernel `Q : S ⇝ 𝓧` which, for each fixed `t`, is a genuine probability measure and
which disintegrates the joint law of `(T(X), X)` under every member. On a standard Borel
sample space the two coincide.

* `hasSufficientKernel_of_isSufficient_dominated` — the **dominated** version: for a family
  dominated by a σ-finite measure on a standard Borel sample space, a sufficient statistic
  admits a θ-free reconstruction kernel. This is the version the rest of the area consumes.
* `hasSufficientKernel_of_isSufficient` — the general standard Borel version, without
  domination. Named planned debt (see below).

**Reference.** Classical theorem on the existence of θ-free regular conditional distributions
given a sufficient statistic, for sample spaces that are Euclidean or, more generally,
standard Borel.

**Proof formalization notes.**
* The dominated route avoids gluing per-event determinations altogether. Fix an equivalent
  countable mixture `ν` of members of the family and let `Q` be the conditional kernel of the
  graph law of `(T, id)` under `ν`, which exists on a standard Borel sample space
  (`MeasureTheory.Measure.condKernel`, requiring `[StandardBorelSpace 𝓧]` and `[Nonempty 𝓧]`
  on the *second* factor of the product; no condition on the value space `S` of the
  statistic). The Halmos–Savage criterion then shows that this single kernel disintegrates
  the graph law of *every* member: the density `dP_θ/dν` is a function of `T`, so tilting the
  disintegration of `ν` by it changes only the first marginal.
* `[Nonempty 𝓧]` is a technical requirement of Mathlib's disintegration API (a Markov kernel
  must have somewhere to put its mass) and is no restriction: the family consists of
  probability measures, so the sample space is nonempty whenever the parameter set is.
* The general (undominated) version genuinely needs the gluing argument — choose
  determinations along a countable generating algebra, repair finite additivity and
  continuity at `∅` on a null set, and extend by Carathéodory — which on standard Borel
  spaces goes through the regularity of the associated conditional distribution functions.
  It is **DEFERRAL-ELIGIBLE**: a named planned debt, pre-agreed for this campaign. Nothing in
  the area consumes it; every downstream user routes through the dominated version.
* Both statements deliver the graph/compProd carrier `HasSufficientKernel` rather than a
  bare reconstruction identity, so that the fiber property of `Sufficiency.Basic` comes for
  free at the point of use.

**Bibliographic comments.** The existence of θ-free conditional distributions given a
sufficient statistic on Euclidean sample spaces is classical; the measure-theoretic treatment
for dominated families is due to P. R. Halmos and L. J. Savage ("Application of the
Radon–Nikodym theorem to the theory of sufficient statistics," *Ann. Math. Statist.* **20**
(1949), 225–241), and the decision-theoretic formulation, in which the reconstruction kernel
is the object of interest, to R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462; "Statistics and subfields," *Ann.
Math. Statist.* **26** (1955), 490–497).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- **Dominated existence of a θ-free reconstruction kernel.** On a standard Borel sample
space, a sufficient statistic for a family dominated by a σ-finite measure admits a single
θ-free Markov kernel disintegrating the graph law of `(T, id)` under every member. -/
theorem hasSufficientKernel_of_isSufficient_dominated [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model is dominated by the σ-finite measure `μ`; classical setup
    (hdom : ∀ θ, P θ ≪ μ)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    HasSufficientKernel P T := by
  sorry

/-- **General existence of a θ-free reconstruction kernel** on a standard Borel sample space,
without any domination assumption.

**DEFERRAL-ELIGIBLE (named planned debt).** The proof requires gluing the per-event
determinations of `IsSufficient` into a single kernel — choosing determinations along a
countable generating algebra and repairing additivity and continuity at `∅` off a null set —
rather than reading the kernel off a disintegration. No result in this area depends on it:
every consumer uses `hasSufficientKernel_of_isSufficient_dominated`. -/
theorem hasSufficientKernel_of_isSufficient [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    HasSufficientKernel P T := by
  sorry

end StatLean.PointEstimation
