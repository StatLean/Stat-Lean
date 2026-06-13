/-
Vector-valued efficient influence functions.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
§25.3 — the definition of efficient influence functions for vector-valued
functionals.
-/
import StatLean.AsymptoticStatistics.Core.EIF
import StatLean.AsymptoticStatistics.Core.PathwiseVec
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Hermitian

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.EIFVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T : Submodule ℝ ↥(L2ZeroMean P)}
variable {k : ℕ}

/-- An efficient influence function tuple `IF : Fin k → L²₀(P)` for a vector
derivative `Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k)` is defined componentwise:
each `IF i` is the efficient influence function for the i-th coordinate
functional.
-/
def IsEfficientInfluenceFunction_vec
    (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k))
    (IF : Fin k → ↥(L2ZeroMean P)) : Prop :=
  ∀ i, IsEfficientInfluenceFunction P T
    (EuclideanSpace.proj i ∘L Dψ) (IF i)

/-- Component extraction from vector EIF. -/
theorem IsEfficientInfluenceFunction_vec_componentwise
    {Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin k)}
    {IF : Fin k → ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction_vec Dψ IF) (i : Fin k) :
    IsEfficientInfluenceFunction P T (EuclideanSpace.proj i ∘L Dψ) (IF i) :=
  hEIF i

end AsymptoticStatistics.Core.EIFVec
