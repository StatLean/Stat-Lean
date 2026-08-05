import StatLean.NonparametricStatistics.RKHS.IntegralOperator
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Mercer kernels and their integral operators

A **Mercer kernel** on a compact metric space `X` is a continuous kernel function
`K : X → X → 𝕜`.  Against a finite Borel measure `μ` on `X`, such a kernel induces the
integral operator `T_K g (x) = ∫ K(x,y) g(y) dμ(y)`, which we package as a continuous
linear endomorphism `mercerCLM` of `L²(X, μ)` (continuity of `K` on the compact square
gives boundedness of the sections uniformly in `x`).

The `L²`-endomorphism only needs continuity of `K`, not positivity, so `mercerCLM` is
defined from a `Continuous` hypothesis alone — the converse direction of Mercer theory
(positivity of `T_K` implies positivity of `K`) then makes sense.

**Bibliographic comments.** J. Mercer, *Functions of positive and negative type and
their connection with the theory of integral equations*, Philos. Trans. Roy. Soc. A
**209** (1909), 415–446.
-/

open ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

variable (𝕜) in
/-- **Mercer kernel**: a jointly continuous kernel function on a compact metric space. -/
structure IsMercerKernel (K : X → X → 𝕜) : Prop where
  /-- Joint continuity on `X × X`.  Constitutive: continuity is what upgrades the
  spectral expansion to uniform convergence. -/
  continuous : Continuous fun p : X × X => K p.1 p.2
  /-- Positive semidefiniteness. -/
  isKernelFun : IsKernelFun K

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- Sections of a jointly continuous kernel are square-integrable against a finite Borel
measure. -/
theorem isL2Symbol_of_continuous {K : X → X → 𝕜}
    -- USER-INPUT: joint continuity of the kernel
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    IsL2Symbol μ K := by
  sorry

/-- The integral operator of a continuous kernel produces square-integrable functions. -/
theorem memLp_integralOp_of_continuous {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    MemLp (integralOp μ K g) 2 μ := by
  sorry

variable (μ) in
/-- **The Mercer integral operator** `T_K : L²(X,μ) → L²(X,μ)`,
`T_K g = [x ↦ ∫ K(x,y) g(y) dμ(y)]`.  Defined for any jointly continuous `K`. -/
noncomputable def mercerCLM {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun g => (memLp_integralOp_of_continuous hKc g).toLp _
      map_add' := by sorry
      map_smul' := by sorry }
    (by sorry)

/-- The defining almost-everywhere description of `mercerCLM`. -/
theorem mercerCLM_coeFn_ae {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    (mercerCLM μ hKc g : X → 𝕜) =ᵐ[μ] integralOp μ K g := by
  sorry

/-- Inner products against `T_K g` can be computed through the pointwise formula. -/
theorem inner_mercerCLM {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g h : Lp 𝕜 2 μ) :
    ⟪h, mercerCLM μ hKc g⟫_𝕜 = ∫ x, conj (h x) * integralOp μ K g x ∂μ := by
  sorry

end StatLean.NonparametricStatistics
