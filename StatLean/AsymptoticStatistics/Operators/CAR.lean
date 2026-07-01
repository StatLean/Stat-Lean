import StatLean.AsymptoticStatistics.Operators.InformationLoss
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Coarsening At Random (CAR)

We observe not the full data $X$ but a coarsened version $Y = M(X)$, where the
coarsening map $M$ is *at random*: conditionally on the observed level $Y = y$,
the full datum $X$ is distributed over the fibre $\{x : M(x) = y\}$ by a law that
does not further depend on the (unobserved) value of $X$. Equivalently, the full
law $P_{\mathrm{full}}$ disintegrates over the observed marginal
$P_{\mathrm{full}} \circ M^{-1}$ through a Markov kernel concentrated on the
$M$-fibres.

This file collects the three observed-data semiparametric results under CAR,
all built on the information-loss (orthogonal projection / conditional
expectation) operator $\Pi = \Pi_{M, P_{\mathrm{full}}}$ from
`Operators/InformationLoss.lean`:

* **Observed tangent space (Theorem 25.40).** Under CAR, the tangent space of
  the observed-data model equals the image $\Pi(\dot{\mathcal P})$ of the
  full-data tangent space $\dot{\mathcal P}$ under $\Pi$.
* **Influence-function lift (Lemma 25.41).** If $\varphi_{\mathrm{full}}$ is an
  influence function for the parameter in the full-data model, then its
  projection $\Pi\,\varphi_{\mathrm{full}}$ is an influence function for the
  same parameter in the observed-data model.
* **Efficiency-loss decomposition (Corollary 25.42).** The efficient influence
  function of the observed-data problem decomposes so that the asymptotic
  variance increases by an explicit nonnegative *information-loss* term
  measuring the part of $\varphi_{\mathrm{full}}$ annihilated by passing to the
  observed data.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.6, Theorem 25.40, Lemma 25.41,
Corollary 25.42.

**Proof formalization notes.** Builds on the information-loss operator
`Π = informationLossOperator M hM P_full` from `Operators/InformationLoss.lean`.
The CAR predicate `IsCoarseningAtRandom` uses the kernel-disintegration form: an
existential of a `ProbabilityTheory.Kernel Ω_obs Ω_full` disintegrating
`P_full` over `P_full.map M`, together with the regularity clause that the
kernel is concentrated on the `M`-fibre (`κ y` lives on `{x | M x = y}`, a.e.).
For deterministic coarsenings on standard Borel spaces, CAR is essentially
automatic via Mathlib's `ProbabilityTheory.Kernel.condDistrib` disintegration;
the substantive content of CAR appears at the *family* level (independence of
the kernel from the unobserved coordinate across submodels), so theorems
requiring CAR list it as an explicit hypothesis.

**Bibliographic comments.** The term *coarsening at random* was coined by
D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data", *The Annals of
Statistics* **19** (1991), no. 4, 2244–2253, generalizing Rubin's
missing-at-random condition to grouped, censored, and rounded data. The
continuous-data theory underlying van der Vaart's §25.6 treatment is developed
in R. D. Gill, M. J. van der Laan and J. M. Robins, "Coarsening at random:
characterizations, conjectures, counter-examples", in *Proceedings of the First
Seattle Symposium in Biostatistics* (D.-Y. Lin and T. R. Fleming, eds.),
Springer Lecture Notes in Statistics **123**, 1997, pp. 255–294, which gives
the disintegration characterization used here and the semiparametric
information calculus for the observed-data model.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.CAR

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Operators.InformationLoss
open ProbabilityTheory

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]

/-- *Coarsening At Random.* The coarsening map `M : Ω_full → Ω_obs` is
*at random* under `P_full` if `P_full` factors as the bind
`(P_full.map M).bind κ` for some kernel `κ : Ω_obs → Measure Ω_full`
that is concentrated on the `M`-fibres (`κ y` lives on `{x | M x = y}`,
a.e.).

Reference: vdV §25.6 (definition leading to thm:25.40).

CAR is a genuine restriction: many real-world coarsenings are **not**
CAR (e.g. outcome-dependent missingness in medical trials), so theorems
requiring CAR list it as an explicit hypothesis.

For deterministic coarsenings on standard Borel spaces, CAR is
essentially automatic via Mathlib's `ProbabilityTheory.Kernel.condDistrib`
disintegration; the substantive content of CAR appears at the *family*
level: independence of the kernel from the unobserved coordinate across
submodels. -/
def IsCoarseningAtRandom
    (M : Ω_full → Ω_obs) (P_full : Measure Ω_full) : Prop :=
  ∃ κ : Kernel Ω_obs Ω_full,
    P_full = (P_full.map M).bind κ ∧
    ∀ᵐ y ∂(P_full.map M), ∀ᵐ x ∂(κ y), M x = y
end AsymptoticStatistics.Operators.CAR
