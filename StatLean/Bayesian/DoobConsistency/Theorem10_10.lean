import StatLean.Bayesian.DoobConsistency.PosteriorMartingale
import StatLean.Bayesian.DoobConsistency.Accessible

/-!
# Theorem 10.10: Doob's posterior consistency theorem

Assembly of vdV Theorem 10.10: for an identifiable model on a standard Borel sample space
with a Polish parameter space, and **any** prior probability measure `π`, the posterior is
strongly consistent at `π`-almost every parameter. No smoothness, dominatedness, or
compactness is assumed.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.4 (Consistency), Theorem 10.10, p. 149 (statement), proof pp. 149–150.

**Proof formalization notes.** Combine `posterior_ae_tendsto_indicator` (Lévy upward, with
the retraction from `exists_measurable_retraction`) over a countable family of balls
(rational radii around a countable dense set of `Θ`), upgrade indicator convergence at the
true parameter to ball-mass convergence to one, and disintegrate the `doobJoint`-a.s.
statement back to `π`-a.e. `θ` with `K θ`-iid-a.s. data (Fubini for `compProd`,
`Measure.ae_ae_of_ae_compProd`). The statement is the ball form of consistency (equivalent
to vdV's weak convergence to `δ_θ` for point limits). vdV's Euclidean sample-space
assumption is generalized to standard Borel; his Lemmas 10.12/10.13 are absorbed into the
explicit retraction of `Accessible.lean`.

**Bibliographic comments.** J. L. Doob, *Application of the theory of martingales*, in *Le
Calcul des Probabilités et ses Applications*, Colloques Internationaux du CNRS **13**,
Paris, 1949, pp. 23–27 — the original martingale proof of posterior consistency off a null
set of parameters. The sharpness of the null-set caveat is discussed by P. Diaconis and
D. Freedman, *On the consistency of Bayes estimates*, Annals of Statistics **14** (1986),
1–26 (with discussion), who construct priors with large inconsistency sets; L. Schwartz,
*On Bayes procedures*, Zeitschrift für Wahrscheinlichkeitstheorie **4** (1965), 10–26,
gives the complementary everywhere-consistency theory under testing conditions.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **Theorem 10.10 (Doob's consistency theorem).** Let `𝓧` be standard Borel, let `Θ` be a
Polish metric parameter space (Borel σ-algebra), and let the model `θ ↦ K θ` be
identifiable. Then for every prior probability measure `π`, the posterior is strongly
consistent at `π`-almost every `θ`: `K θ`-iid-almost-surely, the posterior mass of every
`ε`-ball around `θ` tends to one. -/
theorem doob_consistency [MetricSpace Θ] [PolishSpace Θ] [BorelSpace Θ] [Nonempty Θ]
    [StandardBorelSpace 𝓧]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K]
    -- USER-INPUT: identifiability, `P_θ ≠ P_{θ'}` for `θ ≠ θ'`; vdV Thm 10.10
    (hK_inj : Function.Injective fun θ => K θ)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    ∀ᵐ θ ∂π, StronglyConsistentAt K π θ := by
  sorry

end StatLean.Bayesian
