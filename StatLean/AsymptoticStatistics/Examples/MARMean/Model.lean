import StatLean.AsymptoticStatistics.Core.MassMethod

/-!
# The MAR observation type and the MAR-mean parameter functional

The model-setup half of the concrete-EIF verification template. This file defines
the `(X, R, RY)` observation tuple for missing-at-random data and the
inverse-probability-weighted (IPW) mean functional `marMean_Ψ`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.6 (CAR / MAR);
the observation tuple appears in lem:25.41 and ex:25.43.

Headline declarations: `MARObs`, `marMean_Ψ`.
-/

open MeasureTheory
open scoped InnerProductSpace
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

namespace AsymptoticStatistics.Examples.MARMean

/-- The MAR observation tuple `(X, R, RY)`.

Fields:
- `x` — the always-observed covariate. Without it, no auxiliary
  information is captured.
- `r` — the response indicator (`true` if the response is observed,
  `false` otherwise). Without it, the observed/missing distinction
  is lost.
- `ry` — the partial response `R · Y`: equals `Y` when `r = true`,
  arbitrary (and unused by any well-posed estimator) when `r = false`.
  Without it, the actual outcome data is unrecorded.

Reference: vdV §25.6 (the `(X, Δ, ΔY)` tuple, with `Δ ∈ {0, 1}` the
missingness indicator). -/
structure MARObs (X : Type*) where
  x : X
  r : Bool
  ry : ℝ

/-- Boolean-to-real indicator: `ind true = 1`, `ind false = 0`. Used
to lift the observation indicator `r : Bool` into the AIPW formula
and the IPW functional. -/
def ind : Bool → ℝ
  | true => 1
  | false => 0

@[simp] theorem ind_true : ind true = (1 : ℝ) := rfl
@[simp] theorem ind_false : ind false = (0 : ℝ) := rfl

/-- The σ-algebra on `MARObs X` is the pullback of the product
σ-algebra under the obvious projection. Makes the field accessors
`x`, `r`, `ry` measurable from the product instances on `X`, `Bool`,
and `ℝ`. -/
instance instMeasurableSpaceMARObs
    {X : Type*} [MeasurableSpace X] : MeasurableSpace (MARObs X) :=
  MeasurableSpace.comap (fun o : MARObs X => (o.x, o.r, o.ry))
    (inferInstance : MeasurableSpace (X × Bool × ℝ))

variable {X : Type*} [MeasurableSpace X]
variable {P : Measure (MARObs X)} [IsProbabilityMeasure P]
variable {π : X → ℝ}

/-- The MAR-mean parameter functional: `Q ↦ ∫ (R · Y / π(X)) ∂Q`.

Under MAR with propensity `π(x) = P(R = 1 | X = x)`, this equals
`E_Q[Y]` — the inverse-probability-weighted estimand. The user
proves this identification separately if needed; the present file
only uses the IPW form because it is well-defined for any `Q`. -/
noncomputable def marMean_Ψ (π : X → ℝ) : Measure (MARObs X) → ℝ :=
  fun Q => ∫ o, ind o.r * o.ry / π o.x ∂Q
end AsymptoticStatistics.Examples.MARMean
