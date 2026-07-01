import StatLean.AsymptoticStatistics.Core.MassMethod

/-!
# The MAR observation type and the MAR-mean parameter functional

This file is the model-setup half of the concrete-EIF verification template. It
fixes the data model for a missing-at-random (MAR) problem and the target
parameter whose efficient influence function is verified elsewhere.

A single unit is observed as the tuple $(X, R, RY)$, where $X$ is an
always-observed covariate, $R \in \{0, 1\}$ is the response indicator (with
$R = 1$ meaning the outcome is recorded), and $RY$ is the partial response that
equals the outcome $Y$ when $R = 1$ and is unused otherwise. Writing
$\pi(x) = P(R = 1 \mid X = x)$ for the propensity score, the target functional
is the inverse-probability-weighted (IPW) mean
$$\Psi(Q) = \int \frac{R\,Y}{\pi(X)}\,dQ.$$
Under MAR (equivalently, coarsening-at-random, CAR), this estimand identifies
the marginal outcome mean $E_Q[Y]$; the present file only commits to the IPW
form, which is well defined for every probability measure $Q$ regardless of
whether the identification holds.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.6 (coarsening at random / missing at
random). The $(X, \Delta, \Delta Y)$ observation tuple and the IPW mean
estimand appear at Lemma 25.41 and Example 25.43 (vdV's $\Delta \in \{0, 1\}$ is
the missingness indicator written here as $R$).

**Proof formalization notes.** This module contributes only definitions, no
theorems. The structure `MARObs X` carries the three fields `x`, `r`, `ry`; the
helper `ind : Bool → ℝ` lifts the Boolean indicator `r` to the real weight used
in the IPW formula (`ind true = 1`, `ind false = 0`); and `marMean_Ψ π` is the
functional `Q ↦ ∫ (ind R · RY / π X) ∂Q`. The σ-algebra on `MARObs X` is the
pullback of the product σ-algebra on `X × Bool × ℝ`, so the field accessors are
measurable. The MAR identification $\Psi(Q) = E_Q[Y]$ is not assumed here: the
IPW form is taken as the definition because it is well-posed for arbitrary `Q`,
and the identification is supplied separately by the caller when needed.

**Bibliographic comments.** The IPW estimand and its semiparametric efficiency
theory originate with J. M. Robins, A. Rotnitzky and L. P. Zhao, "Estimation of
regression coefficients when some regressors are not always observed", *Journal
of the American Statistical Association* **89** (427), 1994, 846–866, which
introduced inverse-probability-of-observation weighting and the augmented-IPW
class of estimating equations for data missing at random. van der Vaart §25.6
presents the same construction within the CAR/MAR coarsening framework as a
worked example of the efficient-influence-function calculus; the underlying
coarsening-at-random condition is due to D. F. Heitjan and D. B. Rubin, "Ignorability
and coarse data", *Annals of Statistics* **19** (4), 1991, 2244–2253.
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
