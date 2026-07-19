import StatLean.HypothesisTesting.Tests.Defs
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The conditional exponential family engine

A multiparameter exponential family in which one coordinate `θ` is of interest and the
remaining coordinates `ϑ` are nuisance parameters may be reduced to its sufficient statistic
`(U, T)`, whose joint law is again exponential:
$$ dP^{U,T}_{\theta,\vartheta}(u,t) \;=\; C(\theta,\vartheta)\,
   \exp\bigl(\theta u + \langle \vartheta, t\rangle\bigr)\, d\nu(u,t). $$
This is `IsCanonicalUT`. The engine of the multiparameter theory is the observation that
**conditionally on `T = t`** this collapses to a *one-parameter* exponential family in `θ`,
$$ dP^{U\mid t}_{\theta}(u) \;=\; C_t(\theta)\, e^{\theta u}\, d\nu_t(u), $$
whose base measure `ν_t` depends only on `t` and whose normalizer `C_t(θ)` depends only on
`(t, θ)`: **the nuisance parameter `ϑ` has disappeared**. Every conditional test built on this
family therefore has a `ϑ`-free conditional size, and the one-parameter optimality theory
applies surface by surface.

Contents:

* `IsCanonicalUT` — the canonical joint form of the sufficient statistic;
* `condDistrib_expFamily_of_isCanonicalUT` — the conditional law of `U` given `T = t` is a
  one-parameter exponential family with `(θ,ϑ)`-free base and `ϑ`-free normalizer;
* `condDistrib_eq_of_fst_eq` — the conditional law depends on `(θ, ϑ)` only through `θ`;
* `integral_eq_integral_condDistrib` — the overall power of a test is the average of its
  conditional powers over the law of `T`.

**Reference.** Classical multiparameter exponential-family testing theory; original sources
in the bibliographic comments below.

**Proof formalization notes.**
* The conditional law is Mathlib's `condDistrib U T (P p)`, a Markov kernel `Ξ ⇝ ℝ`
  determined up to `((P p).map T)`-null sets; every conclusion below is therefore stated
  almost everywhere with respect to the law of `T`. Since all members of an exponential
  family with a common base measure are mutually absolutely continuous, the null sets do
  not depend on the parameter, so "a.e. `t`" is unambiguous across the family.
* The tilting computation behind `condDistrib_expFamily_of_isCanonicalUT` — the conditional
  distribution of a `withDensity`-tilted joint law on a standard Borel space is the tilt of
  the conditional distribution — is the sibling-drafted brick
  `StatLean/HypothesisTesting/ForMathlib/CondDistribTilt.lean`; the existential produced
  here (`νt`, `Ct`) is meant to be read off from that brick applied to the joint density
  `exp(θu + ⟪ϑ,t⟫)`, in which the `ϑ`-dependent factor `exp⟪ϑ,t⟫` is `u`-free and hence
  cancels between numerator and normalizer.
* `IsCanonicalUT` is a predicate on a supplied family rather than a bundled structure, so
  that a model may be presented in any parametrization and identified with the canonical
  form only on the parameter set `Ω` actually used. Off `Ω` it says nothing.
* No positivity or σ-finiteness is imposed on the base measures in the statement: they are
  consequences of the canonical form on standard Borel spaces and belong in the proof, not
  the signature.

**Bibliographic comments.** Conditioning on a sufficient statistic to eliminate nuisance
parameters is due to J. Neyman ("Outline of a theory of statistical estimation based on the
classical theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380) and
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37); the completeness theory
that makes the reduction lossless is due to E. L. Lehmann and H. Scheffé ("Completeness,
similar regions, and unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955),
219–236).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 Ξ : Type*} [MeasurableSpace 𝓧]
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [MeasurableSpace Ξ]

/-- **Canonical `(U, T)` exponential family.**

The joint law of the sufficient statistic `(U, T)` under the parameter `(θ, ϑ) ∈ Ω` has
density `C(θ,ϑ)·exp(θ·u + ⟪ϑ, t⟫)` with respect to a fixed parameter-free measure `ν` on
the range of `(U, T)`. Here `U` carries the parameter of interest `θ` and `T` carries the
nuisance parameters `ϑ`.

Edge behaviour: the condition is imposed only for parameters in `Ω`; members of `P` outside
`Ω` are unconstrained. -/
def IsCanonicalUT (P : ℝ × Ξ → Measure 𝓧) (Ω : Set (ℝ × Ξ)) (U : 𝓧 → ℝ) (T : 𝓧 → Ξ)
    (ν : Measure (ℝ × Ξ)) (C : ℝ × Ξ → ℝ) : Prop :=
  ∀ p ∈ Ω, (P p).map (fun x => (U x, T x))
    = ν.withDensity fun z => ENNReal.ofReal (C p * Real.exp (p.1 * z.1 + ⟪p.2, z.2⟫_ℝ))

/-- **The conditional law of `U` given `T = t` is a one-parameter exponential family.**

For a canonical `(U, T)` family there are a base measure `ν_t` on the line depending only on
`t` and normalizers `C_t(θ)` depending only on `(t, θ)` — in particular **not** on the
nuisance parameter `ϑ` — such that, for every parameter in `Ω` and almost every `t`,
`dP^{U|t}_θ(u) = C_t(θ)·e^{θu}·dν_t(u)`.

This is the reduction that makes the whole multiparameter theory one-parameter: the
conditional problem given `T = t` is a one-parameter exponential family in `θ` with natural
statistic `u`. -/
theorem condDistrib_expFamily_of_isCanonicalUT
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    -- LEAN-ONLY: the family members are probability measures; needed for `condDistrib`
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C) :
    ∃ (νt : Ξ → Measure ℝ) (Ct : Ξ → ℝ → ℝ),
      ∀ p ∈ Ω, ∀ᵐ t ∂((P p).map T),
        condDistrib U T (P p) t
          = (νt t).withDensity fun u => ENNReal.ofReal (Ct t p.1 * Real.exp (p.1 * u)) := by
  sorry

/-- **The conditional law does not depend on the nuisance parameter.**

Two parameters of `Ω` sharing the same coordinate of interest `θ` induce the same
conditional distribution of `U` given `T = t`, for almost every `t`. Immediate from
`condDistrib_expFamily_of_isCanonicalUT`, since the right-hand side there mentions the
parameter only through `p.1`. -/
theorem condDistrib_eq_of_fst_eq
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {p q : ℝ × Ξ}
    -- LEAN-ONLY: the family members are probability measures; needed for `condDistrib`
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: both parameters belong to the parameter set
    (hp : p ∈ Ω) (hq : q ∈ Ω)
    -- USER-INPUT: the two parameters agree in the coordinate of interest
    (hfst : p.1 = q.1) :
    ∀ᵐ t ∂((P p).map T), condDistrib U T (P p) t = condDistrib U T (P q) t := by
  sorry

/-- **Overall power is the average of conditional powers.**

For a test `φ` of the sufficient statistic, the power against `P_{θ,ϑ}` is obtained by
averaging the conditional power on each surface `T = t` over the law of `T`:
`E_{θ,ϑ}[φ(U,T)] = ∫ (∫ φ(u,t) dP^{U|t}_θ(u)) dP^T_{θ,ϑ}(t)`.

This is the identity by which maximizing the conditional power surface by surface maximizes
the unconditional power; it is a disintegration statement and needs no exponential-family
structure. -/
theorem integral_eq_integral_condDistrib
    {P : ℝ × Ξ → Measure 𝓧} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {p : ℝ × Ξ} {φ : ℝ × Ξ → ℝ}
    -- LEAN-ONLY: the family members are probability measures; needed for `condDistrib`
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hφ : Measurable φ)
    -- LEAN-ONLY: integrability of the integrand; automatic for critical functions under a
    -- probability measure, but stated in the general form used by the disintegration
    (hint : Integrable (fun x => φ (U x, T x)) (P p)) :
    ∫ x, φ (U x, T x) ∂(P p)
      = ∫ t, (∫ u, φ (u, t) ∂(condDistrib U T (P p) t)) ∂((P p).map T) := by
  sorry

end StatLean.HypothesisTesting
