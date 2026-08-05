import StatLean.NonparametricStatistics.RKHS.IntegralOperator
import StatLean.NonparametricStatistics.RKHS.Basic

/-!
# The range of an integral operator is an RKHS

For a symbol `S : X → Y → 𝕜` with square-integrable sections, the range
`{T_S g : g ∈ L²(Y,μ)}` is a reproducing kernel Hilbert space on `X` with kernel
`K = S □ S*`, and its norm is the range (Sarason) norm
`‖f‖ = inf {‖g‖_{L²} : T_S g = f}`.

**Model.** The kernel of `T_S` is the orthogonal complement of the conjugated sections
`{conj S(x,·)}`, so `T_S` is injective and isometric (for the range norm) on the closed
span of those sections.  We therefore *define* the range space as that closed span
`rangeSpaceCarrier ⊆ L²(Y,μ)`, acting on `X` through `g ↦ T_S g`; the kernel function of
the point `x` is then the section `conj S(x,·)` itself, and the reproducing kernel is
`(S □ S*)`.  The classical statements (range description and infimum formula) are
derived from this model.

**Bibliographic comments.** Range spaces with the lifted norm are due to D. Sarason,
*Sub-Hardy Hilbert Spaces in the Unit Disk* (Wiley, 1994); the identification of the
range of an integral operator as an RKHS goes back to N. Aronszajn, Trans. Amer. Math.
Soc. **68** (1950), §I.8.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [MeasurableSpace Y]
variable {μ : Measure Y}

variable (μ) in
/-- The carrier of the range space of `T_S`: the closed span of the conjugated sections
`conj S(x,·)`, i.e. `(ker T_S)ᗮ ⊆ L²(Y, μ)`. -/
noncomputable def rangeSpaceCarrier (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    Submodule 𝕜 (Lp 𝕜 2 μ) :=
  (Submodule.span 𝕜 (Set.range (symbolConjLp μ S hS))).topologicalClosure

instance (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    CompleteSpace (rangeSpaceCarrier μ S hS) :=
  IsClosed.completeSpace_coe (Submodule.isClosed_topologicalClosure _)

variable (μ) in
/-- The RKHS structure of the range of an integral operator: an element `g` of the
closed span of the conjugated sections acts as the function `T_S g` on `X`.  Provided as
a `def` (used via `letI`), since it depends on the symbol data. -/
noncomputable def rangeSpaceRKHS (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    RKHS 𝕜 (rangeSpaceCarrier μ S hS) X 𝕜 where
  coeCLM :=
    (ContinuousLinearMap.pi fun x => innerSL 𝕜 (symbolConjLp μ S hS x)).comp
      (Submodule.subtypeL _)
  coeCLM_injective := by
    sorry

/-- In the range-space model, members act by the integral operator:
`f x = T_S f (x)`. -/
theorem rangeSpace_apply (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) (x : X) :
    letI := rangeSpaceRKHS μ S hS
    f x = integralOp μ S (f : Lp 𝕜 2 μ) x := by
  sorry

/-- The kernel function of the range space at `x` is the conjugated section
`conj S(x,·)`. -/
theorem rangeSpace_kernelFun (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (x : X) :
    letI := rangeSpaceRKHS μ S hS
    (kernelFun (rangeSpaceCarrier μ S hS) x : Lp 𝕜 2 μ) = symbolConjLp μ S hS x := by
  sorry

/-- **The kernel of the range space is the box product** `S □ S*`. -/
theorem rangeSpace_scalarKernel (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (x z : X) :
    letI := rangeSpaceRKHS μ S hS
    scalarKernel (rangeSpaceCarrier μ S hS) x z = boxProd μ S (symbolAdjoint S) x z := by
  sorry

/-- **The range of the integral operator equals the range space**: every `T_S g` is
realized by a member of the carrier, and conversely. -/
theorem range_integralOp_eq_range_coe (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    letI := rangeSpaceRKHS μ S hS
    Set.range (integralOp μ S)
      = Set.range fun f : rangeSpaceCarrier μ S hS => (f : X → 𝕜) := by
  sorry

/-- **The range norm is the Sarason infimum**:
`‖f‖ = inf {‖g‖_{L²} : T_S g = f}` for `f` in the range space. -/
theorem rangeSpace_norm_eq_sInf (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) :
    letI := rangeSpaceRKHS μ S hS
    ‖f‖ = sInf (norm '' {g : Lp 𝕜 2 μ | integralOp μ S g = (f : X → 𝕜)}) := by
  sorry

/-- The infimum in the Sarason norm is attained, by the representative itself. -/
theorem rangeSpace_norm_attained (S : X → Y → 𝕜) (hS : IsL2Symbol μ S)
    (f : rangeSpaceCarrier μ S hS) :
    letI := rangeSpaceRKHS μ S hS
    integralOp μ S (f : Lp 𝕜 2 μ) = (f : X → 𝕜) := by
  sorry

end StatLean.NonparametricStatistics
