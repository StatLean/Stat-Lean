import StatLean.NonparametricStatistics.RKHS.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Kernel functions (positive semidefinite functions of two variables)

A function `K : X → X → 𝕜` is a **kernel function** if it is Hermitian and every finite
quadratic form `∑ᵢⱼ conj(aᵢ) aⱼ K(xᵢ, xⱼ)` has nonnegative real part.  Over `ℂ` the
Hermitian condition is automatic from positivity of the complex quadratic form; over `ℝ`
it is *not* (e.g. `K = ![![0, 1], ![-1, 0]]` has vanishing real quadratic form), so we
build symmetry into the definition — this matches the classical convention that a
real-valued kernel is required to be positive for all *complex* scalar families.

Main results here:
* `isKernelFun_featureKernel` — a Gram function `(x, y) ↦ ⟪φ x, φ y⟫` of any map
  `φ : X → E` into an inner product space is a kernel function;
* `isKernelFun_scalarKernel` — the reproducing kernel of an RKHS is a kernel function;
* `gramian_posSemidef` / `gramian_posDef_iff_linearIndependent` — the Grammian matrix
  of a finite family of vectors is positive semidefinite, and positive definite iff the
  family is linearly independent.

**Bibliographic comments.** Positive definite functions in this sense were introduced by
E. H. Moore (1935, under the name "positive Hermitian matrices") and J. Mercer,
*Functions of positive and negative type*, Philos. Trans. Roy. Soc. A **209** (1909),
415–446; the Grammian criterion for linear independence is classical (J. P. Gram, 1883).
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}

/-- **Kernel function** (positive semidefinite function): `K : X → X → 𝕜` is Hermitian and
all finite quadratic forms `∑ᵢⱼ conj(aᵢ) aⱼ K(xᵢ, xⱼ)` have nonnegative real part.
Points are not required to be distinct (equivalent to the distinct-points formulation by
merging coefficients). -/
structure IsKernelFun (K : X → X → 𝕜) : Prop where
  /-- Hermitian symmetry: `conj (K x y) = K y x`.  Constitutive: over `ℝ` this is not
  implied by positivity of the real quadratic form and is part of the classical notion. -/
  conj_symm : ∀ x y, conj (K x y) = K y x
  /-- Positivity of all finite quadratic forms. -/
  re_sum_nonneg : ∀ (n : ℕ) (x : Fin n → X) (a : Fin n → 𝕜),
    0 ≤ RCLike.re (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j))

/-- The quadratic form of a kernel function is real: its imaginary part vanishes. -/
theorem IsKernelFun.im_sum_eq_zero {K : X → X → 𝕜} (hK : IsKernelFun K)
    (n : ℕ) (x : Fin n → X) (a : Fin n → 𝕜) :
    RCLike.im (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j)) = 0 := by
  sorry

/-- The diagonal of a kernel function is real with nonnegative real part. -/
theorem IsKernelFun.re_apply_self_nonneg {K : X → X → 𝕜} (hK : IsKernelFun K) (x : X) :
    0 ≤ RCLike.re (K x x) := by
  sorry

/-- Conical combination: `p₁ K₁ + p₂ K₂` is a kernel function for `p₁, p₂ ≥ 0`. -/
theorem IsKernelFun.add_smul {K₁ K₂ : X → X → 𝕜} (h₁ : IsKernelFun K₁)
    (h₂ : IsKernelFun K₂) {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁)  -- USER-INPUT: nonnegative weight
    (hp₂ : 0 ≤ p₂) :  -- USER-INPUT: nonnegative weight
    IsKernelFun (fun x y => (p₁ : 𝕜) * K₁ x y + (p₂ : 𝕜) * K₂ x y) := by
  sorry

/-- Conjugation by a scalar function: `(x, y) ↦ conj (g x) * K x y * g y` is a kernel
function whenever `K` is. -/
theorem IsKernelFun.conj_mul {K : X → X → 𝕜} (hK : IsKernelFun K) (g : X → 𝕜) :
    IsKernelFun (fun x y => conj (g x) * K x y * g y) := by
  sorry

section FeatureKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The **kernel induced by a feature map** `φ : X → E`:
`K(x, y) = ⟪φ x, φ y⟫_𝕜` (conjugate-linear slot first, per Mathlib's convention). -/
noncomputable def featureKernel (φ : X → E) : X → X → 𝕜 := fun x y => ⟪φ x, φ y⟫_𝕜

/-- A Gram function of an arbitrary family of vectors is a kernel function:
the quadratic form is `‖∑ᵢ aᵢ φ(xᵢ)‖² ≥ 0`. -/
theorem isKernelFun_featureKernel (φ : X → E) : IsKernelFun (featureKernel 𝕜 φ) := by
  sorry

end FeatureKernel

section RKHSKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (H) in
/-- The reproducing kernel of an RKHS is its kernel-function Gram representation:
`scalarKernel H = featureKernel 𝕜 (kernelFun H)`. -/
theorem scalarKernel_eq_featureKernel :
    scalarKernel H = featureKernel 𝕜 (kernelFun (X := X) H) := by
  sorry

variable (H) in
/-- The reproducing kernel of an RKHS is a kernel function. -/
theorem isKernelFun_scalarKernel : IsKernelFun (scalarKernel (X := X) H) := by
  sorry

end RKHSKernel

section Gramian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The **Grammian** of a finite family of vectors: the matrix of pairwise inner products
`G i j = ⟪h i, h j⟫_𝕜` (conjugate-linear slot first). -/
noncomputable def gramian {n : ℕ} (h : Fin n → E) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => ⟪h i, h j⟫_𝕜

/-- The Grammian of any finite family is positive semidefinite. -/
theorem gramian_posSemidef {n : ℕ} (h : Fin n → E) : (gramian 𝕜 h).PosSemidef := by
  sorry

/-- The Grammian is positive definite iff the family is linearly independent. -/
theorem gramian_posDef_iff_linearIndependent {n : ℕ} (h : Fin n → E) :
    (gramian 𝕜 h).PosDef ↔ LinearIndependent 𝕜 h := by
  sorry

end Gramian

end StatLean.NonparametricStatistics
