import StatLean.PointEstimation.InformationInequality.CramerRao
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Moments.Covariance

/-!
# The multiparameter information inequality

The one-dimensional covariance inequality `var(δ) ≥ cov(δ, ψ)² / var(ψ)` sharpens to a
quadratic form when several auxiliary functions `ψ_1, …, ψ_r` are available: optimizing the
one-dimensional bound over all linear combinations `∑ a_i ψ_i` gives
$$ \operatorname{var}(\delta) \;\ge\; \gamma^{\mathsf T} C^{-1}\gamma, \qquad
   \gamma_i = \operatorname{cov}(\delta, \psi_i), \quad
   C_{ij} = \operatorname{cov}(\psi_i, \psi_j). $$
Taking the `ψ_i` to be the coordinate scores `∂_{θ_i} \log p_\theta` turns `C` into the
information matrix and `γ` into the gradient of the expectation of `δ`, which is the
information inequality for a vector parameter.

Contents:
* `covariance_matrix_inequality` — the quadratic-form covariance inequality for an
  arbitrary finite family of square-integrable auxiliary functions;
* `multiparameter_cramer_rao` — its specialization to the coordinate scores: the variance of
  a statistic is at least `∇(E_θ δ)ᵀ I(θ)⁻¹ ∇(E_θ δ)`.

**Reference.** Classical multiparameter (matrix) form of the information inequality, and the
quadratic-form covariance inequality it rests on. Original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The quadratic-form inequality is stated at a *fixed* measure: it is a statement of
  second-moment geometry, with no model, parameter or estimand involved. Unbiasedness of `δ`
  plays no role in its proof and is therefore not assumed — it matters only for the *use* of
  the bound, where one wants the right-hand side to depend on `δ` through its expectation
  alone, which happens exactly when each `ψ_i` is uncorrelated with every unbiased estimator
  of zero. Dropping the hypothesis is a strengthening, recorded here to make the deviation
  from the classical phrasing explicit.
* The covariance matrix and the covariance vector are supplied as data together with their
  defining identities, rather than inlined, so the statement reads as the classical
  `γᵀ C⁻¹ γ ≤ var(δ)` and so that consumers may substitute any matrix they have already
  computed.
* Positive definiteness of `C` is a genuine hypothesis: without it the inverse is Lean's
  junk value and the bound carries no content. In the specialization it is positive
  definiteness of the information matrix, which fails exactly when the coordinate scores are
  linearly dependent — the classical degeneracy.
* Partial derivatives in the vector parameter are expressed as one-dimensional derivatives
  along the coordinate directions at `0`, matching the definition of the score vector, so no
  Fréchet-differentiability machinery is needed to state the theorem.

**Bibliographic comments.** The matrix form of the information inequality is due to
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91); the one-dimensional bound it
generalizes was obtained independently by Rao and by H. Cramér (*Mathematical Methods of
Statistics*, Princeton University Press, 1946, §32.3), with earlier forms in M. Fréchet
("Sur l'extension de certaines évaluations statistiques au cas de petits échantillons,"
*Rev. Inst. Int. Statist.* **11** (1943), 182–205) and G. Darmois ("Sur les limites de la
dispersion de certaines estimations," *Rev. Inst. Int. Statist.* **13** (1945), 9–15).
Sharpening the bound by adjoining higher-order derivatives of the density to the family
`ψ_i` is A. Bhattacharyya's ("On some analogues of the amount of information and their use
in statistical estimation," *Sankhyā* **8** (1946), 1–14, 201–218, 315–328).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **The covariance inequality in quadratic form.** For square-integrable `δ` and
auxiliary functions `ψ_1, …, ψ_r` whose covariance matrix `C` is positive definite,
`γᵀ C⁻¹ γ ≤ var(δ)`, where `γ_i = cov(δ, ψ_i)`.

Optimizing the one-dimensional covariance bound over linear combinations `∑ a_i ψ_i` gives
exactly the maximum `max_a (aᵀγ)² / (aᵀ C a) = γᵀ C⁻¹ γ`. -/
theorem covariance_matrix_inequality {r : ℕ} (P : Measure 𝓧)
    -- USER-INPUT: the statement is about a probability measure (a fixed member of a model)
    [IsProbabilityMeasure P]
    (δ : 𝓧 → ℝ) (ψ : Fin r → 𝓧 → ℝ)
    -- USER-INPUT: the statistic has a finite second moment
    (hδ : MemLp δ 2 P)
    -- USER-INPUT: each auxiliary function has a finite second moment
    (hψ : ∀ i, MemLp (ψ i) 2 P)
    (C : Matrix (Fin r) (Fin r) ℝ)
    -- USER-INPUT: `C` is the covariance matrix of the auxiliary functions
    (hC : ∀ i j, C i j = covariance (ψ i) (ψ j) P)
    -- USER-INPUT: that covariance matrix is nonsingular; the classical nondegeneracy
    -- condition, without which the bound is vacuous
    (hCpos : C.PosDef)
    (γ : Fin r → ℝ)
    -- USER-INPUT: `γ` is the vector of covariances of the statistic with the auxiliary
    -- functions
    (hγ : ∀ i, γ i = covariance δ (ψ i) P) :
    γ ⬝ᵥ (C⁻¹ *ᵥ γ) ≤ variance δ P := by
  sorry

/-- **The multiparameter information inequality.** For a dominated family on an
`s`-dimensional parameter with a common support, mean-zero coordinate scores and a positive
definite information matrix, and a square-integrable statistic `δ` whose expectation has
partial derivatives `α_i` obtained by differentiating under the integral sign,
`αᵀ I(θ)⁻¹ α ≤ var_θ(δ)`.

For an unbiased estimator of an estimand `g` the vector `α` is the gradient `∇g(θ)`; in
general it is the gradient of `θ ↦ E_θ δ`, so that a bias contributes through its
gradient. -/
theorem multiparameter_cramer_rao {s : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : EuclideanSpace ℝ (Fin s)) (δ : 𝓧 → ℝ) (α : Fin s → ℝ)
    -- USER-INPUT: on the support, the density is differentiable along each coordinate
    -- direction; classical smoothness condition for a vector parameter
    (hdiff : ∀ i x, 0 < M.density θ x →
      DifferentiableAt ℝ (fun t : ℝ => M.density (θ + t • EuclideanSpace.single i 1) x) 0)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: measurability of each coordinate score, which is built from a `deriv` in
    -- the parameter and therefore carries no measurability in `x` by construction
    (hmeas : ∀ i, AEStronglyMeasurable (fun x => scoreVec M θ x i) μ)
    -- LEAN-ONLY: finiteness of the diagonal information entries as Bochner integrals; the
    -- off-diagonal entries then converge by Cauchy–Schwarz
    (hscore_int : ∀ i, Integrable (fun x => scoreVec M θ x i ^ 2 * M.density θ x) μ)
    -- USER-INPUT: every coordinate score has mean zero; classical regularity condition
    (hmean0 : ∀ i, ∫ x, scoreVec M θ x i * M.density θ x ∂μ = 0)
    -- USER-INPUT: the information matrix is nonsingular; it fails to be so exactly when the
    -- coordinate scores are linearly dependent
    (hIpos : (infoMatrix M μ θ).PosDef)
    -- USER-INPUT: the expectation of the statistic has a partial derivative `α i` in each
    -- coordinate direction
    (hα : ∀ i, HasDerivAt
      (fun t : ℝ => ∫ x, δ x * M.density (θ + t • EuclideanSpace.single i 1) x ∂μ) (α i) 0)
    -- USER-INPUT: those derivatives are obtained by differentiating under the integral sign
    (hswap : ∀ i, α i = ∫ x, δ x * scoreVec M θ x i * M.density θ x ∂μ) :
    α ⬝ᵥ ((infoMatrix M μ θ)⁻¹ *ᵥ α) ≤ variance δ (M.toMeasure μ θ) := by
  sorry

end StatLean.PointEstimation
