import StatLean.NonparametricStatistics.RKHS.KernelFunction
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integral operators, box products and symbol adjoints

Given a measure space `(Y, μ)` and a **symbol** `S : X → Y → 𝕜` with `S(x, ·) ∈ L²(μ)`
for each `x`, the integral operator `T_S g (x) = ∫ S(x,y) g(y) dμ(y)` maps `L²(Y, μ)`
into a space of honest functions on `X`.  Thinking of integral operators as continuous
matrix products, we define the **box product** `(S₁ □ S₂)(x,z) = ∫ S₁(x,y) S₂(y,z) dμ(y)`
and the **adjoint symbol** `S*(y,x) = conj (S x y)`, and prove that `S □ S*` is always a
kernel function — the continuous analogue of `A Aᴴ ⪰ 0`.

**Bibliographic comments.** Integral operators with square-integrable symbols go back to
D. Hilbert and E. Schmidt (1907); the positivity of `S □ S*` is the continuous Schur
factorization, cf. F. Smithies, *Integral Equations* (CUP, 1958).
-/

open ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*} [MeasurableSpace Y]
variable {μ : Measure Y}

variable (μ) in
/-- An **`L²` symbol** on `X × Y`: each section `S(x, ·)` is square-integrable.  This is
the standing hypothesis making the integral operator well-defined on all of `X`. -/
def IsL2Symbol (S : X → Y → 𝕜) : Prop := ∀ x, MemLp (S x) 2 μ

variable (μ) in
/-- The **integral operator** of a symbol: `T_S g (x) = ∫ S(x,y) g(y) dμ(y)`, landing in
genuine functions on `X` (not equivalence classes). -/
noncomputable def integralOp (S : X → Y → 𝕜) (g : Lp 𝕜 2 μ) : X → 𝕜 :=
  fun x => ∫ y, S x y * g y ∂μ

variable (μ) in
/-- The **box product** of two symbols: `(S₁ □ S₂)(x, z) = ∫ S₁(x,y) S₂(y,z) dμ(y)` —
the continuous analogue of the matrix product. -/
noncomputable def boxProd (S₁ : X → Y → 𝕜) (S₂ : Y → Z → 𝕜) : X → Z → 𝕜 :=
  fun x z => ∫ y, S₁ x y * S₂ y z ∂μ

/-- The **adjoint of a symbol**: `S*(y, x) = conj (S x y)` — the continuous analogue of
the conjugate transpose. -/
def symbolAdjoint (S : X → Y → 𝕜) : Y → X → 𝕜 := fun y x => conj (S x y)

/-- Sections of the conjugated symbol are square-integrable when sections of `S` are. -/
theorem IsL2Symbol.conj (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    IsL2Symbol μ fun x y => conj (S x y) := by
  sorry

variable (μ) in
/-- The conjugated section `conj (S x ·)` as an element of `L²(Y, μ)`; satisfies
`T_S g (x) = ⟪symbolConjLp μ S hS x, g⟫`. -/
noncomputable def symbolConjLp (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (x : X) :
    Lp 𝕜 2 μ :=
  ((IsL2Symbol.conj S hS) x).toLp _

/-- The integral operator as an inner product against the conjugated sections. -/
theorem integralOp_eq_inner (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (g : Lp 𝕜 2 μ)
    (x : X) :
    integralOp μ S g x = ⟪symbolConjLp μ S hS x, g⟫_𝕜 := by
  sorry

/-- Pointwise Cauchy–Schwarz bound for the integral operator:
`‖T_S g (x)‖ ≤ ‖S(x,·)‖_{L²} · ‖g‖`. -/
theorem norm_integralOp_le (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) (g : Lp 𝕜 2 μ)
    (x : X) :
    ‖integralOp μ S g x‖ ≤ ‖symbolConjLp μ S hS x‖ * ‖g‖ := by
  sorry

/-- **`S □ S*` is a kernel function**: the box product of a symbol with its adjoint is
positive semidefinite — its quadratic form is `∫ |∑ᵢ conj(aᵢ) S(xᵢ, y)|² dμ(y) ≥ 0`. -/
theorem isKernelFun_boxProd_symbolAdjoint (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    IsKernelFun (boxProd μ S (symbolAdjoint S)) := by
  sorry

/-- The box product with the adjoint is the Gram function of the conjugated sections:
`(S □ S*)(x, z) = ⟪symbolConjLp x, symbolConjLp z⟫`. -/
theorem boxProd_symbolAdjoint_eq_featureKernel (S : X → Y → 𝕜) (hS : IsL2Symbol μ S) :
    boxProd μ S (symbolAdjoint S) = featureKernel 𝕜 (symbolConjLp μ S hS) := by
  sorry

end StatLean.NonparametricStatistics
