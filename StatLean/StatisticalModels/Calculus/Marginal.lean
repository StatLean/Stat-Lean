import StatLean.StatisticalModels.Calculus.Compose

/-!
# Marginals of composite models

How the replication and conditioning operations of the model calculus project back onto their
ingredients:

* `pushforward_condProd_fst` — the covariate marginal of the regression joint law is the
  covariate model;
* `pushforward_condProd_snd` — **the hinge between regression and latent-variable models**: the
  response marginal of the regression joint law is exactly the latent marginalization `mix P K`;
* `condProd_const` — a covariate-free response kernel gives the independent product;
* `pushforward_iid_eval`, `pushforward_iidSeq_eval` — single-coordinate marginals of iid
  replication recover the base model;
* `iid_pushforward` — replication commutes with per-coordinate transformation;
* `pushforward_iidSeq_window` — finite windows of the infinite iid sequence are the `n`-fold
  iid model;
* `iid_indepProd` — iid replication is the constant case of independent replication.

**Reference.** Joint, marginal and conditional model construction: A. C. Davison, *Statistical
Models*, Cambridge University Press, 2003, Chapter 6 (Stochastic Models) (verify §); the product
experiment: L. Le Cam, *Asymptotic Methods in Statistical Decision Theory*, Springer, 1986,
Ch. 3 (verify §).

**Proof formalization notes.** Each lemma is `funext θ` plus one Mathlib brick:
`Measure.fst_compProd` / `Measure.snd_compProd` for the regression marginals,
`Measure.compProd_const` for the product case, `Measure.pi_map_eval` /
`Measure.infinitePi_map_eval` for coordinate marginals (the probability hypothesis makes the
spectator factors have total mass one), `Measure.pi_map_pi` for `iid_pushforward`. Statements
are phrased through the area's `pushforward` so downstream identifiability transfer applies
verbatim.

**Bibliographic comments.** The observation that the second marginal of a disintegrated joint
law is the mixture of the conditional over the marginal is the measure-theoretic form of the
law of total probability; in the statistical-model reading it identifies regression models
observed without covariates with latent-variable (mixture) models — see B. G. Lindsay, *Mixture
Models* (IMS, 1995), §1 (verify §).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

variable {Θ : Type*} {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- The covariate (first) marginal of the regression joint law is the covariate model. -/
theorem pushforward_condProd_fst (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨)
    -- LEAN-ONLY: s-finiteness of the covariate law (satisfied by probability models);
    -- Markov response kernels are USER-INPUT: the model supplies genuine conditional laws
    [∀ θ, SFinite (P θ)] [∀ θ, IsMarkovKernel (K θ)] :
    pushforward (condProd P K) Prod.fst = P := by
  sorry

/-- **Regression ↔ latent marginalization**: the response (second) marginal of the regression
joint law is the latent marginalization `mix P K`. This is the hinge identifying mixture /
mixed-effects models with regression models whose covariate is unobserved. -/
theorem pushforward_condProd_snd (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨)
    -- LEAN-ONLY: s-finiteness of the covariate law (satisfied by probability models)
    [∀ θ, SFinite (P θ)] [∀ θ, IsSFiniteKernel (K θ)] :
    pushforward (condProd P K) Prod.snd = mix P K := by
  sorry

/-- A covariate-free (constant) response kernel makes the regression joint the independent
product of the two models. -/
theorem condProd_const (P : Θ → Measure 𝓧) (Q : Θ → Measure 𝓨)
    [∀ θ, SFinite (P θ)] [∀ θ, SFinite (Q θ)] :
    condProd P (fun θ => Kernel.const 𝓧 (Q θ)) = fun θ => (P θ).prod (Q θ) := by
  sorry

/-- Single-coordinate marginal of the `n`-fold iid model recovers the base model. -/
theorem pushforward_iid_eval (P : Θ → Measure 𝓧)
    -- USER-INPUT: the family consists of probability measures (the spectator coordinates
    -- must carry total mass one); TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] {n : ℕ} (i : Fin n) :
    pushforward (iid P n) (Function.eval i) = P := by
  sorry

/-- Replication commutes with per-coordinate transformation: the iid model of the pushforward
is the coordinatewise pushforward of the iid model. -/
theorem iid_pushforward (P : Θ → Measure 𝓧) {T : 𝓧 → 𝓨}
    -- LEAN-ONLY: measurability of the statistic and s-finiteness; standard regularity
    (hT : Measurable T) [∀ θ, SFinite (P θ)] (n : ℕ) :
    iid (pushforward P T) n = pushforward (iid P n) (fun x => T ∘ x) := by
  sorry

/-- Single-coordinate marginal of the infinite iid sequence model recovers the base model. -/
theorem pushforward_iidSeq_eval (P : Θ → Measure 𝓧)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] (i : ℕ) :
    pushforward (iidSeq P) (Function.eval i) = P := by
  sorry

/-- Finite windows of the infinite iid sequence model are the `n`-fold iid model. -/
theorem pushforward_iidSeq_window (P : Θ → Measure 𝓧)
    -- USER-INPUT: probability family; TPE2 §1.1
    [∀ θ, IsProbabilityMeasure (P θ)] (n : ℕ) :
    pushforward (iidSeq P) (fun x (i : Fin n) => x i) = iid P n := by
  sorry

/-- iid replication is the constant case of independent replication (definitional). -/
theorem iid_indepProd (P : Θ → Measure 𝓧) (n : ℕ) :
    iid P n = indepProd (fun _ : Fin n => P) := rfl

end StatLean.StatisticalModels
