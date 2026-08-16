import StatLean.StatisticalModels.Gaussian.Conditioning
import StatLean.StatisticalModels.GraphicalModels.Core.Coordinates
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The concentration (precision) matrix and Lauritzen's Proposition 5.2

The bridge between the *algebra* of a regular multivariate normal law and the *conditional
independence* vocabulary of `Core.CondIndep`: conditional independence of two coordinates given
all the others is **exactly** a vanishing entry of the inverse covariance matrix.

* `precisionMatrix S := S⁻¹` — Lauritzen's concentration matrix `K = Σ⁻¹`;
* `principalSubmatrix S A` — Lauritzen's `Σ_A`, the principal submatrix on an index block;
* `posDef_submatrix_of_injective`, `posDef_of_fromBlocks_inl/inr` — the positive-definiteness
  plumbing that lets every block statement below derive its own nondegeneracy side conditions
  instead of assuming them;
* **`submatrix_precisionMatrix_fromBlocks_inr_inr` — Lauritzen (C.3)**: the concentration matrix
  of the conditional distribution is obtained from the joint concentration matrix by *deleting*
  the rows and columns of the conditioned-on variables, i.e. it is a principal submatrix of `K`;
  equivalently `condCovMatrix … = (K₂₂)⁻¹` (`condCovMatrix_eq_inv_submatrix_precisionMatrix`,
  the matrix form of Lauritzen (5.10)–(5.11));
* `submatrix_precisionMatrix_fromBlocks_inr_inl` — Lauritzen **(C.4)**, the companion identity
  `K₂₂⁻¹ K₂₁ = −Σ₂₁Σ₁₁⁻¹` consumed by `GraphicalModels.Gaussian.Regression`;
* `map_multivariateGaussian_fromBlocks_eq_prod_iff` — Lauritzen **Corollary C.6** in block form:
  two blocks of a regular joint Gaussian are independent iff the cross-covariance vanishes iff
  the cross-concentration vanishes;
* `gaussianCoords` — the coordinate random vector `(Y_γ)_{γ ∈ ι}` on `EuclideanSpace ℝ ι`, the
  carrier that lets `CondIndepCoords` speak about a Gaussian law;
* **`condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` (HEADLINE, Lauritzen
  Proposition 5.2, p. 129)**: for `Σ` regular and `γ ≠ μ`,
  `Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}} ⟺ k_{γμ} = 0`.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**: §5.1.3 "Conditional independence", p. 129 —
Proposition 5.2 and the displays (5.10), (5.11); Appendix C, pp. 256–257 — Proposition C.5 with
(C.2) and the identities (C.3) `K₁₁⁻¹ = Σ₁₁ − Σ₁₂Σ₂₂⁻Σ₂₁` and (C.4) `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻` on
p. 256, the determinant identity (C.5) and Corollary C.6 on p. 257
(`Lauritzen §5.1.3`, `Lauritzen App. C`). Page numbers and item kinds follow
`notes/factor_graphical/books.md`.

*Generalized versus ordinary inverse.* Lauritzen writes `Σ₂₂⁻`, "an arbitrary generalized
inverse", in (C.2)–(C.4), but his own proof of Proposition C.5 assumes `Σ` regular and then
`Σ₂₂⁻ = Σ₂₂⁻¹`. We state the regular case only, matching both his proof and the standing
hypothesis of §5.1.3; the pseudoinverse form is already a named future debt of the Gaussian
slice (D-G1 in `Gaussian/Conditioning`).

**Proof formalization notes.**

*Book vs Lean, orientation.* Lauritzen partitions `X = (X₁, X₂)` and conditions on the
**second** block (Proposition C.5 computes the law of `X₁` given `X₂`), so his (C.3) reads
`K₁₁⁻¹ = Σ₁₁ − Σ₁₂Σ₂₂⁻¹Σ₂₁`. The repo's Gaussian slice conditions on the **first** block:
`condCovMatrix S₁₁ S₁₂ S₂₂ = S₂₂ − S₁₂ᵀ S₁₁⁻¹ S₁₂` is the law of block `ι₂` given block `ι₁`
(`Gaussian.Conditioning`). Every book identity is therefore transcribed with the two blocks
swapped: (C.3) becomes `K₂₂ = (condCovMatrix …)⁻¹` and (C.4) becomes
`K₂₂⁻¹ K₂₁ = −condMeanMatrix …`. Nothing else changes.

*Book vs Lean, regularity.* Lauritzen says "`Σ` regular"; `Matrix.inv` is a junk-valued total
function (`0` at singular matrices) and `multivariateGaussian` degenerates to a Dirac mass off
the positive-semidefinite cone, so every statement below carries an explicit `PosDef`
hypothesis. `PosDef` rather than `PosSemidef`: an inverse is taken in every one of them.

*Routes (do not re-derive).*

| Step | Consumed from |
|---|---|
| Schur complement of a `PosDef` block | `Matrix.PosDef.fromBlocks₁₁` (`LinearAlgebra/Matrix/PosDef.lean:541`) — note the real name is on `PosDef`, **not** `PosSemidef`, and it needs `[Invertible A]`, supplied by `Matrix.PosDef.isUnit.invertible` |
| the four blocks of `(fromBlocks A B C D)⁻¹` | `Matrix.invOf_fromBlocks₁₁_eq` (`SchurComplement.lean:285`) + `Matrix.invOf_eq_nonsing_inv` |
| Schur complement is invertible | `Matrix.invertibleOfFromBlocks₁₁Invertible` (`SchurComplement.lean:315`) |
| Gaussian conditional law (exact disintegration) | `compProd_gaussianCondKernel` (G3.4, `Gaussian.Conditioning`) |
| zero cross-block ⇒ product law | `multivariateGaussian_fromBlocks_prod` (G2.9, `Gaussian.Marginal`) — the atom of every separation proof |
| block marginals | `multivariateGaussian_map_blockFst` / `_blockSnd` (`Gaussian.Marginal`) |
| covariance of a Gaussian law | `covMatrix_multivariateGaussian` (`ForMathlib.CovarianceMatrix`) |
| `Fin`/`Sum` and `ι`/`Sum` index transport | `multivariateGaussian_map_reindex` (`Gaussian.FinCorridor`) — the **only** corridor |

*Route for the headline (Proposition 5.2).* With `R := ↥({γ,μ}ᶜ)` (the rest) and
`P := ↥{γ,μ}` (the pair), transport `S` along `Equiv.sumCompl (· ∈ ({γ,μ} : Finset ι)ᶜ)`
through `multivariateGaussian_map_reindex` to the sum index `R ⊕ P`. Then:
1. `compProd_gaussianCondKernel` writes the law as `N(m_R, S_RR) ⊗ₘ gaussianCondKernel …`, whose
   conditional covariance `condCovMatrix S_RR S_RP S_PP` does **not** depend on the conditioning
   value — this is what makes the disintegration a *product* kernel and hence `CondIndep`;
2. (C.3) above identifies that conditional covariance's inverse with the `2 × 2` principal
   submatrix `K_P` of the joint concentration matrix — Lauritzen (5.10);
3. `map_multivariateGaussian_fromBlocks_eq_prod_iff` (Corollary C.6) applied *inside* the
   conditional law splits it into a product over the two coordinates iff its cross-covariance
   vanishes iff `k_{γμ} = 0` — the explicit `2 × 2` inverse (5.11) turns one into the other;
4. the `CondIndep` witnesses are the two coordinate marginals of the conditional kernel
   (`Kernel.map` of `gaussianCondKernel` along the two projections), Markov by
   `Kernel.IsMarkovKernel.map`.
Lauritzen's own proof is exactly this ("almost a direct consequence of Proposition C.5 and its
proof", p. 129), so no shortcut is being taken.

*Law transfer, deliberately not asserted.* Everything here is stated for the **canonical**
coordinate vector `gaussianCoords` on the Gaussian's own sample space `EuclideanSpace ℝ ι`.
Transferring to an arbitrary random vector `Y : Ω → ι → ℝ` whose law is `N(m, S)` requires the
fact that `CondIndep` depends only on the joint law of `(f, g, h)`; that is a `Core.CondIndep`
statement, is not in this file's scope, and is therefore **not** assumed anywhere below.

**Bibliographic comments.** The characterisation of conditional independence by zeros of the
inverse covariance is due to A. P. Dempster, "Covariance selection," *Biometrics* **28** (1972),
157–175, who introduced the term *covariance selection* for the resulting model class; the
matrix identities (C.3)–(C.5) are the classical Schur-complement calculus (I. Schur, 1917),
standard in multivariate analysis since T. W. Anderson, *An Introduction to Multivariate
Statistical Analysis*, Wiley, 1958, §2.5. The name *concentration matrix* is Dempster's;
*precision matrix* is the Bayesian synonym.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **concentration matrix** (a.k.a. precision matrix) `K = Σ⁻¹` of a covariance matrix
(Lauritzen §5.1.3, p. 129: "Assume the covariance to be regular such that the concentration
matrix `K = Σ⁻¹` is well defined").

Edge behaviour: `Matrix.inv` is total, with the junk value `0` at every singular matrix
(`Matrix.nonsing_inv_apply_not_isUnit`). So `precisionMatrix S = 0` whenever `S` is singular,
and *every* theorem about it carries an explicit `S.PosDef` hypothesis — `PosDef` and not
`PosSemidef`, because the book's standing assumption is that `Σ` is regular. -/
noncomputable def precisionMatrix (S : Matrix ι ι ℝ) : Matrix ι ι ℝ := S⁻¹

theorem precisionMatrix_def (S : Matrix ι ι ℝ) : precisionMatrix S = S⁻¹ := rfl

/-- The **principal submatrix** `Σ_A` of `S` on an index block (Lauritzen's notation
`Σ_{Γ∖{γ}}`, `Σ_{Γ∖{γ,μ}}`, used in (5.12)).

Edge behaviour: for `A = ∅` this is the empty matrix, whose determinant is `1` — which is the
convention (5.12) needs when `Γ = {γ, μ}`. -/
noncomputable def principalSubmatrix (S : Matrix ι ι ℝ) (A : Finset ι) : Matrix A A ℝ :=
  S.submatrix (fun a => (a : ι)) (fun a => (a : ι))

end Defs

section CoordinateVector

/-- The **coordinate random vector** `Y = (Y_γ)_{γ ∈ ι}` on `EuclideanSpace ℝ ι` — the identity
map, read through the `WithLp` type synonym as a function on the index set. This is the carrier
that turns a Gaussian *measure* into the *random vector* `Y ∼ N_{|Γ|}(ξ, Σ)` of Lauritzen
§5.1.3, so that `CondIndepCoords` applies to it.

Edge behaviour: none — it is `WithLp.ofLp`, a measurable equivalence onto `ι → ℝ`
(`WithLp.measurable_ofLp`); in particular no `Fintype ι` is needed to state it. -/
def gaussianCoords {ι : Type*} : EuclideanSpace ℝ ι → ι → ℝ := fun x => WithLp.ofLp x

theorem measurable_gaussianCoords {ι : Type*} :
    Measurable (gaussianCoords (ι := ι)) :=
  WithLp.measurable_ofLp 2 _

end CoordinateVector

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- The concentration matrix of a regular covariance is itself positive definite. -/
theorem precisionMatrix_posDef
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) :
    (precisionMatrix S).PosDef :=
  hS.inv

/-- The diagonal of the concentration matrix is strictly positive — the well-definedness fact
behind the scaling `c_{γμ} = k_{γμ}/√(k_{γγ}k_{μμ})` of Lauritzen p. 130. -/
theorem precisionMatrix_diag_pos
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) (i : ι) :
    0 < precisionMatrix S i i :=
  (precisionMatrix_posDef hS).diag_pos

/-- The concentration matrix is symmetric. -/
theorem precisionMatrix_transpose
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) :
    (precisionMatrix S)ᵀ = precisionMatrix S := by
  have hsymm : Sᵀ = S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hS.isHermitian
  rw [precisionMatrix_def, Matrix.transpose_nonsing_inv, hsymm]

/-- Entrywise form of `precisionMatrix_transpose`: `k_{γμ} = k_{μγ}`. -/
theorem precisionMatrix_apply_comm
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) (i j : ι) :
    precisionMatrix S i j = precisionMatrix S j i :=
  (congrFun (congrFun (precisionMatrix_transpose hS) i) j).symm

/-- `Σ` is recovered from `K`: the concentration and covariance matrices are mutually inverse
(Lauritzen §5.1.3, p. 129). -/
theorem precisionMatrix_precisionMatrix
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hS : S.PosDef) :
    precisionMatrix (precisionMatrix S) = S := by
  rw [precisionMatrix_def, precisionMatrix_def,
    Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hS.isUnit)]

end Basic

section PosDefPlumbing

/-- LEAN-ONLY (`ForMathlib` candidate; the pin has `Matrix.PosSemidef.submatrix` for an arbitrary
index map and `Matrix.posSemidef_submatrix_equiv`, but no positive-definite analogue): a
principal submatrix of a positive definite matrix along an **injective** index map is positive
definite. Injectivity is essential — a repeated index makes the extension-by-zero of a nonzero
vector cancel. -/
theorem posDef_submatrix_of_injective {n m : Type*} [Fintype n] [Fintype m]
    {M : Matrix n n ℝ}
    -- LEAN-ONLY: the ambient positive definiteness
    (hM : M.PosDef) {f : m → n}
    -- LEAN-ONLY: injectivity of the index selection; see the docstring
    (hf : Function.Injective f) :
    (M.submatrix f f).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hM.1.submatrix f, fun x hx => ?_⟩
  set z : n → ℝ := Function.extend f x 0 with hz
  have hzf : ∀ a, z (f a) = x a := fun a => hf.extend_apply x 0 a
  have hz0 : ∀ i, i ∉ Set.range f → z i = 0 := fun i hi => by
    simp [hz, Function.extend_apply' _ _ _ hi]
  -- summing a function supported on the range of `f` is summing its pullback
  have hsum : ∀ g : n → ℝ, (∀ i, i ∉ Set.range f → g i = 0) →
      ∑ i, g i = ∑ a, g (f a) := by
    intro g hg
    rw [← Finset.sum_image (f := g) (g := f) (s := (Finset.univ : Finset m))
      (fun a _ b _ h => hf h)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    exact hg i (by simpa [Finset.mem_image, Set.mem_range] using hi)
  have hzne : z ≠ 0 := by
    intro h
    refine hx (funext fun a => ?_)
    have := congrFun h (f a)
    rwa [hzf a] at this
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hzne
  simp only [star_trivial] at hpos ⊢
  refine lt_of_lt_of_eq hpos ?_
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [hsum (fun i => z i * ∑ j, M i j * z j) (fun i hi => by simp [hz0 i hi])]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hzf a, hsum (fun j => M (f a) j * z j) (fun j hj => by simp [hz0 j hj])]
  exact congrArg _ (Finset.sum_congr rfl fun b _ => by rw [hzf b])

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  {S₁₁ : Matrix ι₁ ι₁ ℝ} {S₁₂ : Matrix ι₁ ι₂ ℝ} {S₂₂ : Matrix ι₂ ι₂ ℝ}

/-- LEAN-ONLY: the first diagonal block of a regular joint covariance is regular. Derived, not
assumed — this is what lets the block theorems below take only the *joint* `PosDef` hypothesis
that Lauritzen states ("`Σ` regular"), rather than laundering the block nondegeneracy in. -/
theorem posDef_of_fromBlocks_inl
    -- LEAN-ONLY: regular joint covariance; Lauritzen §5.1.3, p. 129
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    S₁₁.PosDef := by
  have hsub : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).submatrix Sum.inl Sum.inl = S₁₁ := by
    ext i j; simp
  exact hsub ▸ posDef_submatrix_of_injective hJ (Sum.inl_injective (β := ι₂))

/-- LEAN-ONLY: the second diagonal block of a regular joint covariance is regular. -/
theorem posDef_of_fromBlocks_inr
    -- LEAN-ONLY: regular joint covariance; Lauritzen §5.1.3, p. 129
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    S₂₂.PosDef := by
  have hsub : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).submatrix Sum.inr Sum.inr = S₂₂ := by
    ext i j; simp
  exact hsub ▸ posDef_submatrix_of_injective hJ (Sum.inr_injective (α := ι₁))

/-- LEAN-ONLY: the Schur complement of a regular block covariance is regular — the conditional
covariance of a regular joint normal is itself regular, which is what makes the conditional
concentration matrix of (C.3) well defined. -/
theorem posDef_condCovMatrix
    -- LEAN-ONLY: regular joint covariance; Lauritzen App. C, (C.3)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (condCovMatrix S₁₁ S₁₂ S₂₂).PosDef := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(posSemidef_condCovMatrix hJ.posSemidef h₁₁).1, fun x hx => ?_⟩
  have hne : (-((S₁₁⁻¹ * S₁₂) *ᵥ x)) ⊕ᵥ x ≠ 0 := by
    intro h
    exact hx (funext fun b => congrFun h (Sum.inr b))
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hJ).2 hne
  rw [dotProduct_mulVec, ← hconj, Matrix.schur_complement_eq₁₁ S₁₂ S₂₂ _ _ h₁₁.1,
    neg_add_cancel, dotProduct_zero, zero_add, ← dotProduct_mulVec, hconj] at hpos
  exact hpos

end PosDefPlumbing

section BlockIdentities

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Lauritzen (C.3), the conditional-concentration identity** (the equation is in the proof of
Proposition C.5, App. C, p. 256; the reading quoted here — "the concentration matrix of the
conditional distribution is obtained from the concentration matrix of the joint distribution by
deleting rows and columns corresponding to the variables conditioned upon" — is the remark on
p. 257). The same matrix is `K_{\{γ,μ\}}` of Lauritzen (5.10), p. 129.

In the repo's orientation the conditioned-on block is `ι₁`, so "deleting the rows and columns of
the conditioning variables" is the principal submatrix at `Sum.inr`. -/
theorem submatrix_precisionMatrix_fromBlocks_inr_inr
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.3)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inr
      = (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  haveI : Invertible (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := hJ.isUnit.invertible
  haveI : Invertible (S₂₂ - S₁₂ᵀ * ⅟S₁₁ * S₁₂) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S₁₁ S₁₂ S₁₂ᵀ S₂₂
  rw [precisionMatrix_def, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
  simp only [Matrix.invOf_eq_nonsing_inv]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, condCovMatrix]

/-- **Lauritzen (C.3) read as (5.10)–(5.11)**: the conditional covariance is the inverse of the
principal submatrix of the joint concentration matrix on the conditioned block. -/
theorem condCovMatrix_eq_inv_submatrix_precisionMatrix
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.3)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    condCovMatrix S₁₁ S₁₂ S₂₂
      = ((precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inr)⁻¹ := by
  rw [submatrix_precisionMatrix_fromBlocks_inr_inr S₁₁ S₁₂ S₂₂ hJ,
    Matrix.nonsing_inv_nonsing_inv _
      (Matrix.isUnit_iff_isUnit_det _ |>.mp (posDef_condCovMatrix hJ).isUnit)]

/-- **Lauritzen (C.4)** (App. C, p. 256: `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻`), transcribed with the blocks
swapped: the off-diagonal block of the concentration matrix, scaled by the conditional
covariance, is minus the Gaussian regression matrix `condMeanMatrix S₁₁ S₁₂ = S₂₁S₁₁⁻¹`. This is
the identity that `GraphicalModels.Gaussian.Regression` turns into `β_{γμ} = −k_{γμ}/k_{γγ}`. -/
theorem submatrix_precisionMatrix_fromBlocks_inr_inl
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.4)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inl
      = -((condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹ * condMeanMatrix S₁₁ S₁₂) := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  haveI : Invertible (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := hJ.isUnit.invertible
  haveI : Invertible (S₂₂ - S₁₂ᵀ * ⅟S₁₁ * S₁₂) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S₁₁ S₁₂ S₁₂ᵀ S₂₂
  rw [precisionMatrix_def, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
  simp only [Matrix.invOf_eq_nonsing_inv]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply,
    condCovMatrix, condMeanMatrix, ← Matrix.mul_assoc]

/-- **Lauritzen Corollary C.6, matrix half** (p. 257: "If `Σ` is regular, this holds if and only
if `K₁₂ = 0`"): the cross-concentration block vanishes exactly when the cross-covariance block
does. Immediate from (C.4), both factors being invertible. -/
theorem submatrix_precisionMatrix_fromBlocks_inl_inr_eq_zero_iff
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen Cor. C.6
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inl Sum.inr = 0
      ↔ S₁₂ = 0 := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  have hcc : (condCovMatrix S₁₁ S₁₂ S₂₂).PosDef := posDef_condCovMatrix hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  haveI : Invertible (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := hJ.isUnit.invertible
  haveI : Invertible (S₂₂ - S₁₂ᵀ * ⅟S₁₁ * S₁₂) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S₁₁ S₁₂ S₁₂ᵀ S₂₂
  have hblock : (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inl Sum.inr
      = -(S₁₁⁻¹ * S₁₂ * (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹) := by
    rw [precisionMatrix_def, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₁₁_eq]
    simp only [Matrix.invOf_eq_nonsing_inv]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
      condCovMatrix]
  have hu1 : IsUnit S₁₁.det := (Matrix.isUnit_iff_isUnit_det _).mp h₁₁.isUnit
  have hu2 : IsUnit (condCovMatrix S₁₁ S₁₂ S₂₂).det := (Matrix.isUnit_iff_isUnit_det _).mp hcc.isUnit
  rw [hblock, neg_eq_zero]
  constructor
  · intro h
    have h2 : S₁₁ * (S₁₁⁻¹ * S₁₂ * (condCovMatrix S₁₁ S₁₂ S₂₂)⁻¹) * condCovMatrix S₁₁ S₁₂ S₂₂
        = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one] at h2
    exact h2
  · intro h; simp [h]

/-- **Lauritzen Corollary C.6** (p. 257) in the repo's measure-level form: two blocks of a
regular joint Gaussian are independent — the joint law transported to the product space is the
product of the block marginals — iff the cross-concentration block vanishes.

The `⟸` direction is `multivariateGaussian_fromBlocks_prod` (G2.9) after
`submatrix_precisionMatrix_fromBlocks_inl_inr_eq_zero_iff` turns `K₁₂ = 0` into `S₁₂ = 0`; the
`⟹` direction reads the covariance off the product law with `covMatrix_multivariateGaussian`
(the covariance of a product measure is block diagonal). -/
theorem map_multivariateGaussian_fromBlocks_eq_prod_iff
    (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen Cor. C.6
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
          (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        = (multivariateGaussian m₁ S₁₁).prod (multivariateGaussian m₂ S₂₂)
      ↔ (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inl Sum.inr = 0 := by
  have h₁₁ : S₁₁.PosDef := posDef_of_fromBlocks_inl hJ
  have h₂₂ : S₂₂.PosDef := posDef_of_fromBlocks_inr hJ
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  -- the diagonal joint covariance is a genuine covariance
  have hJ0 : (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₁ ι₂ ℝ)ᵀ S₂₂).PosSemidef := by
    have := (Matrix.PosDef.fromBlocks₁₁ (A := S₁₁) (0 : Matrix ι₁ ι₂ ℝ) S₂₂ h₁₁).mpr
      (by simpa using h₂₂.posSemidef)
    simpa using this
  have hsplit : (multivariateGaussian (blockPair m₁ m₂)
        (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₁ ι₂ ℝ)ᵀ S₂₂)).map
          (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
      = (multivariateGaussian m₁ S₁₁).prod (multivariateGaussian m₂ S₂₂) := by
    simpa using multivariateGaussian_fromBlocks_prod m₁ m₂ S₁₁ S₂₂ h₁₁.posSemidef h₂₂.posSemidef
  rw [submatrix_precisionMatrix_fromBlocks_inl_inr_eq_zero_iff S₁₁ S₁₂ S₂₂ hJ]
  constructor
  · -- read the covariance off the product law
    intro hprod
    have hlaw : multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)
        = multivariateGaussian (blockPair m₁ m₂)
            (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₁ ι₂ ℝ)ᵀ S₂₂) :=
      ext_of_map_sumMeasEquivProd (hprod.trans hsplit.symm)
    have hcov := congrArg covMatrix hlaw
    rw [covMatrix_multivariateGaussian _ _ hJ.posSemidef,
      covMatrix_multivariateGaussian _ _ hJ0] at hcov
    ext i j
    have := congrFun (congrFun hcov (Sum.inl i)) (Sum.inr j)
    simpa using this
  · intro h
    subst h
    exact hsplit

end BlockIdentities

section Proposition52

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **HEADLINE — Lauritzen Proposition 5.2** (*Graphical Models*, 1996, §5.1.3, p. 129).

Let `Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ` regular, and let `K = {k_{αβ}} = Σ⁻¹` be its concentration
matrix. Then for two distinct coordinates `γ ≠ μ`,
`Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}}  ⟺  k_{γμ} = 0`.

This is the fundamental relation on which every model of Lauritzen ch. 5 rests: "Corresponding
to the different Markov properties studied in Chapter 3, we have multivariate normal models
defined through restricting particular elements in suitable concentration matrices to be equal
to zero" (p. 129).

The conditional independence is stated with the contracted `CondIndepCoords` of
`Core.Coordinates` for the canonical coordinate vector `gaussianCoords` on the Gaussian's own
sample space; see the module docstring for why law transfer is deliberately not assumed. The
degenerate case `Γ = {γ, μ}` (empty conditioning block) is included and is Corollary C.6.

The conditioning block is written `Finset.univ \ {i, j}` rather than `({i, j} : Finset ι)ᶜ` so
that this theorem lands **syntactically on the nose** of `Undirected.Markov.IsPairwiseMarkov`,
which is how `Gaussian.Model` consumes it. -/
theorem condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen Prop. 5.2, p. 129
    (hij : i ≠ j) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j} (Finset.univ \ {i, j})
      ↔ precisionMatrix S i j = 0 := by
  sorry

end Proposition52

end StatLean.StatisticalModels.GraphicalModels
