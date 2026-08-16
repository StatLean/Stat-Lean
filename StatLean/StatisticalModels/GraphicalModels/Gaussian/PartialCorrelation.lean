import StatLean.StatisticalModels.GraphicalModels.Gaussian.Precision
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.Sqrt

/-!
# Partial correlations — the scaled concentration matrix

The statistical reading of the entries of the concentration matrix `K = Σ⁻¹` (Lauritzen §5.1.3,
p. 129–130, the unnumbered displays following Proposition 5.2):

* the **diagonal** entries are reciprocal conditional variances, `k_{γγ} = V(Y_γ ∣ Y_{Γ∖{γ}})⁻¹`;
* the **off-diagonal** entries, scaled so that `K` has unit diagonal, are minus the *partial
  correlation coefficients*.

* `partialCorr S γ μ` — Lauritzen's `ρ_{γμ ∣ Γ∖{γ,μ}} = −k_{γμ}/√(k_{γγ}k_{μμ})`;
* `partialCorr_eq_zero_iff` and **`condIndepCoords_gaussianCoords_iff_partialCorr_eq_zero`** —
  the chain `ρ = 0 ⟺ k_{γμ} = 0 ⟺ Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}}`;
* `precisionMatrix_diag_eq_inv_condCovMatrix` — the conditional-variance identity, p. 129;
* `neg_inv_apply_div_sqrt_eq` + `neg_precision_div_sqrt_eq_condCorr` — the reason the *minus
  sign* is there: on a two-element block, minus the scaled entry of the inverse is the ordinary
  correlation of the conditional law;
* `partialCorr_sq` — Lauritzen **(5.12)**, the determinant formula for `ρ²`.

## ⚠ The sign

**The partial correlation is MINUS the scaled precision entry.** Lauritzen defines
`c_{γμ} = k_{γμ}/√(k_{γγ}k_{μμ})` (the entries of `K` scaled to unit diagonal) and then states,
p. 130: "Then `c_{γμ}`, the off-diagonal elements in `C`, are equal to the **negative** partial
correlation coefficients", `ρ_{γμ ∣ Γ∖{γ,μ}} = −c_{γμ}`. Verified against the book text.

Sanity check that fixes the sign beyond doubt (`|Γ| = 2`, `Σ = !![a, b; b, d]`): here
`K = (ad − b²)⁻¹ · !![d, −b; −b, a]`, so
`−k_{12}/√(k_{11}k_{22}) = (b/(ad−b²)) · (ad−b²)/√(ad) = b/√(ad)`, the ordinary correlation —
whereas `+k_{12}/√(k_{11}k_{22})` would give its negative.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**, §5.1.3, pp. 129–130: the identity
`k_{γγ} = V(Y_γ ∣ Y_{Γ∖{γ}})⁻¹` (unnumbered, foot of p. 129), the definition of `c_{γμ}` and the
partial correlation `ρ_{γμ ∣ Γ∖{γ,μ}} = −c_{γμ}` (unnumbered displays, p. 130), and the
determinant identity (5.12) (`Lauritzen §5.1.3`).

**Proof formalization notes.**

*Book vs Lean, edge behaviour.* `Real.sqrt` is `0` on negatives and `x / 0 = 0` in Lean, so
`partialCorr` is total; under `S.PosDef` the diagonal `k_{γγ}` is strictly positive
(`precisionMatrix_diag_pos`), the square root is positive, and the definition is the book's. All
substantive statements therefore carry `hS : S.PosDef`.

*Book vs Lean, the diagonal.* Lauritzen scales `C` to have unit diagonal, i.e. `c_{γγ} = 1`, so
his convention forces `ρ_{γγ} = −1`. We record that as `partialCorr_self` rather than special-
casing the definition: the book's formula is used verbatim, degenerate diagonal and all.

*Book vs Lean, the two-variable displays of p. 130.* Lauritzen also records
`V(Y_γ ∣ Y_{Γ∖{γ,μ}}) = k_{μμ}/(k_{γγ}k_{μμ} − k_{γμ}²)` and
`Cov(Y_γ, Y_μ ∣ Y_{Γ∖{γ,μ}}) = −k_{γμ}/(k_{γγ}k_{μμ} − k_{γμ}²)`. These are the entries of the
explicit `2 × 2` inverse (5.11) and are *not* stubbed separately: `neg_inv_apply_div_sqrt_eq`
packages exactly the combination of them that the partial correlation needs, and the full
entrywise form is `Matrix.inv_def` + `Matrix.adjugate_fin_two` after a `Fin 2` reindexing.

*Routes (do not re-derive).*

| Step | Consumed from |
|---|---|
| `k_{γγ} > 0` | `precisionMatrix_diag_pos` (`Gaussian.Precision`) |
| the conditional concentration matrix is a principal submatrix of `K` | `submatrix_precisionMatrix_fromBlocks_inr_inr` — Lauritzen (C.3) (`Gaussian.Precision`) |
| `ρ = 0 ⟺ k_{γμ} = 0 ⟺ CI` | `condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` — Prop. 5.2 (`Gaussian.Precision`) |
| the `2 × 2` inverse | `Matrix.inv_def`, `Matrix.adjugate_fin_two_of`, `Matrix.det_fin_two_of` after transporting `ι₂ ≃ Fin 2` (`Fintype.equivFinOfCardEq`) |
| `det Σ > 0` for a regular covariance | `Matrix.PosDef.det_pos` (`Analysis/Matrix/PosDef.lean:85`) |
| (5.12) determinant bookkeeping | `Matrix.det_fromBlocks₁₁` (`SchurComplement.lean:369`) — this is Lauritzen (C.5), `det Σ = det Σ₂₂ / det K₁₁`, applied four times |

**Bibliographic comments.** Partial correlation is K. Pearson and G. U. Yule's (1896–1907); the
identification of the scaled inverse covariance with minus the partial correlations is classical
multivariate analysis (T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
Wiley, 1958, §2.5). Its use as the *parametrisation* of a graphical model — zeros of the scaled
inverse being the missing edges — is A. P. Dempster's covariance selection, "Covariance
selection," *Biometrics* **28** (1972), 157–175.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **partial correlation coefficient** `ρ_{γμ ∣ Γ∖{γ,μ}}` of two coordinates given all the
others (Lauritzen §5.1.3, p. 130, unnumbered display):
`ρ_{γμ ∣ Γ∖{γ,μ}} = −k_{γμ}/√(k_{γγ}k_{μμ}) = −c_{γμ}`, where `c` is `K` scaled to unit diagonal.

**The minus sign is the book's** — see the module docstring for the verification and a numerical
check.

Edge behaviour: total, by Lean's `Real.sqrt` (zero on negatives) and `x / 0 = 0`. If `S` is
singular then `precisionMatrix S = 0` and `partialCorr S γ μ = 0` vacuously, so every
substantive statement below assumes `S.PosDef`. On the diagonal the book's own scaling gives
`partialCorr S γ γ = −1` (`partialCorr_self`), not `1`. -/
noncomputable def partialCorr (S : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  -(precisionMatrix S i j) / Real.sqrt (precisionMatrix S i i * precisionMatrix S j j)

end Defs

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- Symmetry of the partial correlation, from symmetry of the concentration matrix. -/
theorem partialCorr_comm
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialCorr S i j = partialCorr S j i := by
  sorry

/-- Edge behaviour of the book's scaling on the diagonal: `c_{γγ} = 1`, hence
`ρ_{γγ} = −c_{γγ} = −1`. Recorded, not patched — the definition follows Lauritzen verbatim. -/
theorem partialCorr_self
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i : ι) :
    partialCorr S i i = -1 := by
  sorry

/-- **The partial correlation vanishes exactly when the concentration entry does.** The scaling
`√(k_{γγ}k_{μμ})` is strictly positive for a regular `Σ`, so it cannot create or destroy zeros.
No `γ ≠ μ` hypothesis is needed: on the diagonal both sides are false. -/
theorem partialCorr_eq_zero_iff
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialCorr S i j = 0 ↔ precisionMatrix S i j = 0 := by
  sorry

/-- **Lauritzen Proposition 5.2 in partial-correlation form** (§5.1.3, pp. 129–130): for a
regular `Σ` and `γ ≠ μ`, conditional independence of the two coordinates given all the others is
equivalent to a vanishing *partial correlation*. Composition of Proposition 5.2 with
`partialCorr_eq_zero_iff`. -/
theorem condIndepCoords_gaussianCoords_iff_partialCorr_eq_zero
    (m : EuclideanSpace ℝ ι)
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen Prop. 5.2, p. 129
    (hij : i ≠ j) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j} ({i, j} : Finset ι)ᶜ
      ↔ partialCorr S i j = 0 := by
  sorry

end Basic

section ConditionalVariance

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **The conditional-variance identity** (Lauritzen §5.1.3, p. 129, unnumbered display):
"the diagonal elements `k_{γγ}` are reciprocals of the conditional variances, given the remaining
variables", `k_{γγ} = V(Y_γ ∣ Y_{Γ∖{γ}})⁻¹`.

Stated on the sum index with a **singleton** conditioned block `ι₂` (Lauritzen's `{γ}`), where
`condCovMatrix S₁₁ S₁₂ S₂₂` is the `1 × 1` conditional covariance, i.e. the conditional variance
`V(Y_γ ∣ Y_{Γ∖{γ}})`; the general-block version is `condCovMatrix_eq_inv_submatrix_precisionMatrix`
(Lauritzen (C.3)), of which this is the `1 × 1` instance. -/
theorem precisionMatrix_diag_eq_inv_condCovMatrix
    -- LEAN-ONLY: the conditioned block is Lauritzen's singleton `{γ}`; `Subsingleton` plus the
    -- witness `a` is the type-level form of `|{γ}| = 1`, under which a `1 × 1` matrix inverse is
    -- the scalar inverse
    [Subsingleton ι₂]
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 129
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) (a : ι₂) :
    precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a)
      = (condCovMatrix S₁₁ S₁₂ S₂₂ a a)⁻¹ := by
  sorry

end ConditionalVariance

section TwoBySignTrap

/-- **The algebraic heart of the sign convention.** For a positive definite `2 × 2` matrix `M`,
minus the off-diagonal entry of `M⁻¹`, scaled by the geometric mean of the diagonal entries of
`M⁻¹`, is the ordinary correlation built from `M` itself.

This is `−c = ρ` stripped of all probability: apply it to `M := ` the conditional covariance
matrix on a two-element block, whose inverse is the corresponding principal submatrix of `K` by
Lauritzen (C.3), and Lauritzen's p. 130 display drops out. -/
theorem neg_inv_apply_div_sqrt_eq {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
    {M : Matrix ι₂ ι₂ ℝ}
    -- USER-INPUT: regular covariance; Lauritzen §5.1.3, p. 130
    (hM : M.PosDef)
    -- USER-INPUT: exactly two variables — Lauritzen's pair `{γ, μ}`; the identity is **false**
    -- for larger blocks, where the two scalings differ by the remaining variables
    (hcard : Fintype.card ι₂ = 2) {a b : ι₂}
    -- USER-INPUT: `γ ≠ μ`; Lauritzen §5.1.3, p. 130
    (hab : a ≠ b) :
    -(M⁻¹ a b) / Real.sqrt (M⁻¹ a a * M⁻¹ b b) = M a b / Real.sqrt (M a a * M b b) := by
  sorry

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Lauritzen p. 130, `ρ_{γμ ∣ Γ∖{γ,μ}} = −c_{γμ}`** in block form: for a joint Gaussian whose
non-conditioned block is exactly the pair `{γ, μ}`, minus the scaled entry of the concentration
matrix equals the correlation of the *conditional* law of `(Y_γ, Y_μ)` given all the rest.

The cardinality hypothesis is essential and is the book's setting, not an artefact: for a larger
second block the left-hand side conditions on the remaining coordinates of that block as well,
and the two sides genuinely differ. -/
theorem neg_precision_div_sqrt_eq_condCorr
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef)
    -- USER-INPUT: the non-conditioned block is exactly Lauritzen's pair `{γ, μ}`
    (hcard : Fintype.card ι₂ = 2) {a b : ι₂}
    -- USER-INPUT: `γ ≠ μ`; Lauritzen §5.1.3, p. 130
    (hab : a ≠ b) :
    -(precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr b))
          / Real.sqrt (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a)
              * precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr b) (Sum.inr b))
      = condCovMatrix S₁₁ S₁₂ S₂₂ a b
          / Real.sqrt (condCovMatrix S₁₁ S₁₂ S₂₂ a a * condCovMatrix S₁₁ S₁₂ S₂₂ b b) := by
  sorry

end TwoBySignTrap

section Identity512

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- **Lauritzen (5.12)** (§5.1.3, p. 130): the squared partial correlation in terms of principal
minors of the covariance matrix,
`ρ²_{γμ ∣ Γ∖{γ,μ}} = c²_{γμ} = 1 − (det Σ · det Σ_{Γ∖{γ,μ}}) / (det Σ_{Γ∖{γ}} · det Σ_{Γ∖{μ}})`.

Lauritzen derives it from (C.5) applied four times; `principalSubmatrix` is his `Σ_A`, with the
empty-matrix determinant `1` covering the case `Γ = {γ, μ}` (where the identity reduces to the
familiar `ρ² = 1 − det Σ / (σ_{γγ}σ_{μμ})`). -/
theorem partialCorr_sq
    -- USER-INPUT: `Σ` regular; Lauritzen (5.12), p. 130
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen (5.12), p. 130
    (hij : i ≠ j) :
    partialCorr S i j ^ 2
      = 1 - (S.det * (principalSubmatrix S ({i, j} : Finset ι)ᶜ).det)
            / ((principalSubmatrix S ({i} : Finset ι)ᶜ).det
                * (principalSubmatrix S ({j} : Finset ι)ᶜ).det) := by
  sorry

end Identity512

end StatLean.StatisticalModels.GraphicalModels
