import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral transport between independence hypotheses and canonical products

Theorem-agnostic wrappers translating abstract-sample-space independence
hypotheses into integrals over explicit canonical product measures. For an
independent family $X_i : \Omega \to \beta_i$,
$$ \int_\Omega G\bigl((X_i(\omega))_i\bigr)\, d\mu
   \;=\; \int G \, d\Bigl(\bigotimes_i (X_i)_\# \mu\Bigr), $$
with a variant carrying a passenger product factor, and the
introduce/eliminate-auxiliary-randomness identity for a pair of independent
maps: if $A \perp B$ and $B$ has law $\rho$, then
$$ \int_\Omega G(A(\omega), B(\omega))\, d\mu
   \;=\; \int_{\Omega \times \gamma} G(A(\omega'), z)\, d(\mu \otimes \rho). $$
These are the three moves every symmetrization assembly file and every
downstream consumer (VC, chaining) uses to move between "signs on `Ω`" and
"signs as a product coordinate".

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3 (joint law of an independent family;
footnote 7 on enlarging the probability space with independent signs). Pure
plumbing — no numbered theorem.

**Proof formalization notes.** All three lemmas are wraps of pin-verified
Mathlib bricks: `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`,
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`,
`MeasureTheory.MeasurePreserving.prod`, and `MeasureTheory.integral_map`.
Measurability of the integrand is taken as `AEStronglyMeasurable` with respect
to the *pushforward* measure — the natural hypothesis for `integral_map`.
Mathlib-only imports; candidate upstream. Named-sorry fallback of this work
item: `integral_prod_eq_integral_pi_prod` (the passenger-coordinate
transport); the two single-map transports are direct wraps.

**Bibliographic comments.** The identification of an independent family with
the product of its marginal laws is Kolmogorov's construction (*Grundbegriffe
der Wahrscheinlichkeitsrechnung*, 1933); the "enlarge the space by an
independent auxiliary sequence" device is standard in Banach-space probability
(Ledoux–Talagrand, *Probability in Banach Spaces*, 1991, Ch. 6; HDP §6.3
Notes).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Transport an integral of a function of an independent family to the
product of the marginal laws (HDP §6.3: the joint law of an independent
family is the product of the marginals). -/
theorem integral_eq_integral_pi_map {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : (i : ι) → Ω → β i}
    -- LEAN-ONLY: a.e.-measurability of the family; matches
    -- `iIndepFun_iff_map_fun_eq_pi_map`'s hypothesis shape
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    -- USER-INPUT: independent family; HDP §6.3
    (h_indep : iIndepFun X μ)
    {G : ((i : ι) → β i) → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward; the natural
    -- `integral_map` side condition
    (hG : AEStronglyMeasurable G (Measure.pi fun i => μ.map (X i))) :
    ∫ ω, G (fun i => X i ω) ∂μ = ∫ y, G y ∂(Measure.pi fun i => μ.map (X i)) := by
  sorry

/-- Transport with a passenger product factor: an integral over `μ.prod ρ` of
a function of the independent family in the first coordinate equals the
integral over the canonical product `(⊗ᵢ (Xᵢ)#μ).prod ρ`. Named-sorry debt
candidate of this work item. -/
theorem integral_prod_eq_integral_pi_prod {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : (i : ι) → Ω → β i}
    -- LEAN-ONLY: measurability of the family
    (h_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent family; HDP §6.3
    (h_indep : iIndepFun X μ)
    {γ : Type*} {mγ : MeasurableSpace γ} {ρ : Measure γ} [IsProbabilityMeasure ρ]
    {G : (((i : ι) → β i) × γ) → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward product
    (hG : AEStronglyMeasurable G ((Measure.pi fun i => μ.map (X i)).prod ρ)) :
    ∫ p, G (fun i => X i p.1, p.2) ∂(μ.prod ρ)
      = ∫ q, G q ∂((Measure.pi fun i => μ.map (X i)).prod ρ) := by
  sorry

/-- Replace on-`Ω` auxiliary randomness by a product extension: if `A ⊥ B`
and `B` has law `ρ`, integrating `G (A ω, B ω)` over `Ω` equals integrating
`G (A ω, z)` over `μ.prod ρ` (HDP §6.3 footnote 7: signs independent of the
data may be realized on an enlarged product space). -/
theorem integral_indepFun_eq_integral_prod {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
    {A : Ω → α} {B : Ω → γ} {ρ : Measure γ}
    -- LEAN-ONLY: measurability of the data map
    (hA : Measurable A)
    -- LEAN-ONLY: measurability of the auxiliary map
    (hB : Measurable B)
    -- USER-INPUT: auxiliary randomness independent of the data; HDP §6.3 footnote 7
    (hAB : IndepFun A B μ)
    -- USER-INPUT: law of the auxiliary randomness; HDP §6.3
    (hBlaw : μ.map B = ρ)
    {G : α × γ → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward product
    (hG : AEStronglyMeasurable G ((μ.map A).prod ρ)) :
    ∫ ω, G (A ω, B ω) ∂μ = ∫ p, G (A p.1, p.2) ∂(μ.prod ρ) := by
  sorry

end StatLean.ConcentrationInequalities
