import StatLean.AsymptoticStatistics.Core.TangentAbstract
import StatLean.AsymptoticStatistics.Core.QMDPath

/-!
# Influence functions, efficient influence functions, and pathwise differentiability

The first two definitions (`IsInfluenceFunction`, `IsEfficientInfluenceFunction`)
are pure Hilbert: they take an abstract derivative CLF `dψ : T →L[ℝ] ℝ` and
do not mention curves. The third (`PathwiseDifferentiableAt`) is the
*curve-based* assertion that `ψ : Measure Ω → ℝ` has a derivative; it uses
the `QMDPath` machinery from `Core/QMDPath.lean`.

Reference: van der Vaart, *Asymptotic Statistics*, §25.3 — the definitions
of influence function, efficient influence function, and pathwise
differentiability following lem:25.14.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.Pathwise

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (T : Submodule ℝ ↥(L2ZeroMean P))

/-- An *influence function* at `P` for a pathwise derivative `dψ : T →L[ℝ] ℝ`
is an element `IF ∈ ↥(L2ZeroMean P)` whose `L²(P)` inner product against any
tangent direction `g ∈ T` recovers `dψ g`.

Reference: vdV §25.3, definition of influence function (paragraph after the
definition of pathwise differentiability). The book states it as
`IF ∈ L²₀(P)` with `PIFg = ψ̇_P(g)` for all `g ∈ 𝒫̇_P`; in Lean we use the
inner-product form which is definitionally equal.

Edge behavior: when `T = ⊥`, the universal quantifier is over the singleton
`{0}` and `dψ 0 = 0 = ⟪IF, 0⟫`, so every `IF` is trivially an influence
function. Matches the book's convention that a degenerate tangent space
imposes no constraint. -/
def IsInfluenceFunction (dψ : T →L[ℝ] ℝ) (IF : ↥(L2ZeroMean P)) : Prop :=
  ∀ g : T, ⟪IF, (g : ↥(L2ZeroMean P))⟫_ℝ = dψ g

/-- An *efficient influence function* at `P` for a derivative `dψ : T →L[ℝ] ℝ`
is an influence function that lies inside the tangent space `T`.

Reference: vdV §25.3, definition of efficient influence function (paragraph
following the definition of influence function). The book observes that the
EIF, when it exists, is the orthogonal projection of any influence function
onto the (closed) tangent space — that uniqueness/projection theorem is
`Core/EIF.eif_eq_orthogonalProjection`.

Edge behavior: when `T = ⊥`, the only EIF is `0`, and `0` is an influence
function iff `dψ` is identically zero. -/
def IsEfficientInfluenceFunction
    (dψ : T →L[ℝ] ℝ) (IF : ↥(L2ZeroMean P)) : Prop :=
  IsInfluenceFunction P T dψ IF ∧ IF ∈ T

/-- A statistical functional `ψ : Measure Ω → ℝ` is *pathwise differentiable*
at `P` relative to the tangent space `T` iff there exists a continuous-linear
derivative `dψ : T →L[ℝ] ℝ` such that for every `QMDPath` at `P` whose
score lies in `T`, the difference quotient `(ψ(γ.curve t) - ψ P)/t`
converges to `dψ ⟨γ.score, _⟩` as `t → 0`.

Reference: vdV §25.3, definition immediately following lem:25.14 (curve-based).
Its faithful formulation depends on the QMD curves of `Core/QMDPath.lean`.

Edge behavior: when `T = ⊥`, the only QMDPath with score in `T` has score
`0`, and the difference quotient must tend to `dψ 0 = 0` — which forces
`ψ` to be locally constant along any such path through `P`. -/
structure PathwiseDifferentiableAt
    (ψ : Measure Ω → ℝ) where
  /-- vdV §25.3: the pathwise derivative as a continuous
  linear functional on the tangent space. -/
  derivative : T →L[ℝ] ℝ
  /-- vdV §25.3: the difference-quotient limit holds along
  every QMDPath at `P` whose score lies in `T`. -/
  derivative_spec :
    ∀ (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P),
      ∀ (h_in_T : (γ.score : ↥(L2ZeroMean P)) ∈ T),
        Filter.Tendsto (fun t : ℝ => (ψ (γ.curve t) - ψ P) / t)
          (nhdsWithin 0 {0}ᶜ) (nhds (derivative ⟨γ.score, h_in_T⟩))

end AsymptoticStatistics.Core.Pathwise
