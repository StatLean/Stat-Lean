import StatLean.StatisticalModels.Identifiability.Transfer
import StatLean.PointEstimation.Sufficiency.Defs

/-!
# Adapter: sufficiency is exactly lossless coarsening

The flagship identifiability adapter: reducing data to a **sufficient** statistic loses no
identification power. Against `StatLean.PointEstimation.Sufficiency` (imported, never
redefined):

* `pushforward_eq_statLaw` — the calculus' `pushforward` is PointEstimation's `statLaw`
  (definitional);
* `identifiable_pushforward_iff_of_hasSufficientKernel` — for `T` with a sufficient kernel,
  `Identifiable (pushforward P T) ↔ Identifiable P`: the backward direction is the generic
  destroy-direction; the forward direction reconstructs each `P θ` from the law of `T` through
  the θ-free kernel (marginalizing the graph disintegration), so distinct laws of `T` are
  forced;
* `identifiesTarget_pushforward_iff_of_hasSufficientKernel` — the target version.

Together with `Identifiability.Transfer` this completes the picture: coarsening can only
destroy identification, and sufficiency is precisely the case in which it destroys none.

**Reference.** TPE2 §1.6 (sufficiency via θ-free conditional distributions); the
reconstruction-from-the-statistic reading: P. R. Halmos and L. J. Savage, *Ann. Math.
Statist.* **20** (1949), 225–241.

**Proof formalization notes.** The forward direction takes `Measure.snd` of the graph identity
`(P θ).map (fun x => (T x, x)) = statLaw P T θ ⊗ₘ Q` (the reconstruction move documented in
`PointEstimation.Sufficiency.BayesianBridge`): equal statistic laws then force equal
reconstructions, i.e. equal models. Markov-ness of `Q` and probability of the members enter
through `Measure.snd_compProd`.

**Bibliographic comments.** Sufficiency as the coarsening that preserves all statistical
content is Fisher's original reading ("On the mathematical foundations of theoretical
statistics," *Phil. Trans. R. Soc. A* **222** (1922), 309–368); the kernel form is
Halmos–Savage.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

open StatLean.PointEstimation

variable {Θ : Type*} {𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- The calculus' pushforward model is PointEstimation's law-of-the-statistic
(definitional). -/
theorem pushforward_eq_statLaw (P : Θ → Measure 𝓧) (T : 𝓧 → S) :
    pushforward P T = statLaw P T := rfl

/-- **Sufficiency is lossless coarsening**: for a statistic with a sufficient kernel, the
reduced model is identifiable iff the full model is (TPE2 §1.6; Halmos–Savage 1949). -/
theorem identifiable_pushforward_iff_of_hasSufficientKernel {P : Θ → Measure 𝓧} {T : 𝓧 → S}
    -- USER-INPUT: T admits a θ-free sufficient kernel (regular-conditional sufficiency);
    -- TPE2 §1.6
    (hT : HasSufficientKernel P T)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] :
    Identifiable (pushforward P T) ↔ Identifiable P := by
  sorry

/-- Target version: sufficiency preserves target identifiability in both directions. -/
theorem identifiesTarget_pushforward_iff_of_hasSufficientKernel {Γ : Type*}
    {P : Θ → Measure 𝓧} {T : 𝓧 → S} {ψ : Θ → Γ}
    -- USER-INPUT: sufficiency of T; TPE2 §1.6
    (hT : HasSufficientKernel P T)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] :
    IdentifiesTarget (pushforward P T) ψ ↔ IdentifiesTarget P ψ := by
  sorry

end StatLean.StatisticalModels
