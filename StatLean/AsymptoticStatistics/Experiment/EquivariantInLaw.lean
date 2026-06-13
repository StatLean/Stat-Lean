import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Equivariant-in-law randomized estimators in the Gaussian shift experiment

The defining notion `IsEquivariantInLaw` for vdV §8.4 Proposition 8.4
("Convolution structure for equivariant-in-law estimators in the Gaussian
shift experiment"): a randomized estimator `T` is equivariant-in-law for
estimating `Ah` if the distribution of `T − Ah` under `h` does not depend on
`h`.

We encode `T` as a Markov kernel `Kernel ℝᵏ ℝᵈ`. Given `X ∼ N(h, Σ)` (modelled
by `multivariateGaussian h Σ`) and randomization kernel `T`, the law of `T(X)`
at parameter `h` is `T ∘ₘ (multivariateGaussian h Σ)`; the law of `T − Ah` is
then this pushed forward by the deterministic translation by `−Ah`.
Equivariance: this translated law is the same probability measure `L` for every
`h`. `L` is the **null distribution** of `T`.

This file states only the definition plus the Skolemized accessor
`IsEquivariantInLaw.nullDist` (characterised by
`IsEquivariantInLaw.map_sub_eq_nullDist`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics
namespace EquivariantInLaw

variable {k d : ℕ}

/-- **Equivariance-in-law for a randomized estimator** (vdV §8.4).

`T` is a randomized estimator of `A·h` based on observing `X ∼ N(h, S)`,
encoded as a Markov kernel `Kernel ℝᵏ ℝᵈ`. `T` is **equivariant-in-law**
iff for every `h`, the distribution of `T(X) − A·h` (under `X ∼ N(h, S)`)
equals one common probability measure `L`. `L` is called the **null
distribution** of `T`. (`S` here is the covariance matrix vdV writes as
`Σ`; `Σ` is reserved in Lean.) -/
structure IsEquivariantInLaw
    (T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    (A : Matrix (Fin d) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) : Prop where
  /-- vdV §8.4: there exists a probability measure `L`
  on `ℝᵈ` such that for every `h ∈ ℝᵏ`, the law of `T(X) − A·h` under
  `X ∼ N(h, S)` equals `L`. Equivalently, the pushforward of `T ∘ₘ
  multivariateGaussian h S` by `y ↦ y − A·h` is `L` for all `h`. -/
  invariant_law :
    ∃ L : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure L ∧
      ∀ h : EuclideanSpace ℝ (Fin k),
        (T ∘ₘ (multivariateGaussian h S)).map
            (fun y => y - (WithLp.equiv 2 (Fin d → ℝ)).symm
              (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h)))
          = L

/-- The **null distribution** of an equivariant-in-law estimator
(vdV §8.4, "invariant law `L`"). Skolemized from
`IsEquivariantInLaw.invariant_law`; characterised by
`IsEquivariantInLaw.map_sub_eq_nullDist`. -/
noncomputable def IsEquivariantInLaw.nullDist
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    {A : Matrix (Fin d) (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ}
    (h : IsEquivariantInLaw T A S) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  h.invariant_law.choose

/-- The null distribution is a probability measure. -/
instance IsEquivariantInLaw.isProbabilityMeasure_nullDist
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    {A : Matrix (Fin d) (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ}
    (h : IsEquivariantInLaw T A S) :
    IsProbabilityMeasure h.nullDist :=
  h.invariant_law.choose_spec.1

/-- Characterising property of the null distribution: for every `h`, the
pushforward of the kernel composition by the translation `y ↦ y − A·h`
equals `nullDist`. -/
theorem IsEquivariantInLaw.map_sub_eq_nullDist
    {T : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))}
    {A : Matrix (Fin d) (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ}
    (hT : IsEquivariantInLaw T A S) (h : EuclideanSpace ℝ (Fin k)) :
    (T ∘ₘ (multivariateGaussian h S)).map
        (fun y => y - (WithLp.equiv 2 (Fin d → ℝ)).symm
          (A.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h)))
      = hT.nullDist :=
  hT.invariant_law.choose_spec.2 h

end EquivariantInLaw
end AsymptoticStatistics
