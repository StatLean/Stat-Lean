import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimator
import StatLean.AsymptoticStatistics.Core.PathwiseVec
import StatLean.AsymptoticStatistics.Core.EIFVec
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Vector-valued regular-estimator predicate

The Hájek-style regular-estimator definition (vdV §25.3.2) extended to
vector-valued functionals, together with a basic reduction lemma.

Main declarations: `IsRegularEstimator_broad_vec`,
`IsRegularEstimator_broad_vec.shift`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimatorVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Hájek-style vector regular-estimator predicate (all-paths / broad form).**

A sequence of vector estimators `T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin k)`
is regular at `P` relative to a tangent set `T_set`, with limit law `L`.

This is the *all-paths* (`∀ curve`) strengthening of the vdV-canonical
chosen-family form `IsRegularEstimator_vec`: it requires the weak-convergence
conclusion for **every** realising `QMDPath` with score `g`, not merely for one
*selected* submodel per direction. As a written proposition `broad ⇒ canonical`
holds trivially, so the broad form is a strictly stronger hypothesis; it is kept
as a **labeled internal variant** for the convolution-theorem proof, while the
unlabeled canonical name `IsRegularEstimator_vec` denotes the vdV p.365 form. The
two are equivalent via `isRegularEstimator_vec_implies_broad` (and its trivial
converse).

Reference: vdV §25.3.2 (generalized to vector codomain), all-paths strengthening.
-/
def IsRegularEstimator_broad_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {k : ℕ}
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k))
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    (_hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L] : Prop :=
  ∀ (g : ↥(L2ZeroMean P))
    (_hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P)
    (_hscore : curve.score = g),
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))))
      L

/-- **Hájek-style vector regular-estimator predicate (vdV §25.3.2 p.365 canonical
form).**

A sequence of vector estimators `T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin k)` is
*regular* at `P` relative to the tangent set `T_set`, with limit law `L`, iff
there exists a chosen family of `QMDPath`s — one *selected* submodel per score
direction `g ∈ tangentSpace T_set` — such that along each chosen path the rescaled
estimator, recentered at the perturbed truth, converges weakly to the **same**
limit law `L`:

```
√n • (T_n − ψ((chosenFamily g hg).curve ((√n)⁻¹)))  ⇀  L .
```

This is the verbatim vdV form: vdV §25.3.2 p.365 reads "for every `g ∈ Ṗ_P`,
**write `P_{t,g}` for a submodel** …", i.e. *one selected submodel per score
direction*. It is the vector analogue of the scalar
`IsRegularEstimator_narrow`, differing only in the codomain
(`EuclideanSpace ℝ (Fin k)` in place of `ℝ`, hence `•` for `*`) and the `_vec`
efficient-influence-function tuple.

The all-paths (`∀ curve`) strengthening is `IsRegularEstimator_broad_vec`. The two
are equivalent: `broad ⇒ canonical` trivially (instantiate `chosenFamily` at any
realiser, e.g. `canonicalPath`), and `canonical ⇒ broad` via
`isRegularEstimator_vec_implies_broad` (Cramér–Wold reduction to the scalar
chosen-family reverse direction). The headline convolution theorem
`semiparametric_convolution_theorem_vec` consumes **this** canonical form, so the
presented hypothesis byte-matches the book.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3.2
(regular-estimator definition, paragraph preceding Theorem 25.20), generalized to
vector codomain. -/
def IsRegularEstimator_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {k : ℕ}
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k))
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    (_hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L] : Prop :=
  ∃ chosenFamily :
      ∀ (g : ↥(L2ZeroMean P)),
        (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier → QMDPath P,
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      (chosenFamily g hg).score = g) ∧
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n => (chosenFamily g hg).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ ((chosenFamily g hg).curve ((Real.sqrt n)⁻¹)))))
        L)

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T_set : TangentSpec P}
variable {k : ℕ}
variable {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
variable {IF_eff : Fin k → ↥(L2ZeroMean P)}
variable {hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ}
variable {hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
                  hψ.derivative IF_eff}
variable {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)}
variable {L : Measure (EuclideanSpace ℝ (Fin k))}

/-- **Direct unfolding of `IsRegularEstimator_broad_vec`.** -/
theorem IsRegularEstimator_broad_vec.shift [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L)
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P) (hscore : curve.score = g) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))))
      L :=
  hReg g hg curve hscore

end AsymptoticStatistics.LowerBounds.RegularEstimatorVec
