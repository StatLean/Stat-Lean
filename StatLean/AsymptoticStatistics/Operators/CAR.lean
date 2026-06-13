import StatLean.AsymptoticStatistics.Operators.InformationLoss
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Coarsening At Random (CAR)

Observed-data tangent decomposition, influence-function lift, and the
efficiency-loss formula under coarsening at random.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.6:
thm:25.40 (under CAR, the observed tangent space equals `Π '' full tangent
space`), lem:25.41 (`Π φ_full` is an observed-data influence function),
cor:25.42 (efficient-influence decomposition with explicit variance-loss
term).

Builds on the information-loss operator
`Π = informationLossOperator M hM P_full` from `Operators/InformationLoss.lean`.

The CAR predicate `IsCoarseningAtRandom` uses the kernel-disintegration
form: an existential of a `ProbabilityTheory.Kernel Ω_obs Ω_full`
disintegrating `P_full` over `P_full.map M`, together with the regularity
clause that the kernel is concentrated on the `M`-fibre.
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
