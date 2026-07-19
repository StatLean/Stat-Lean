import StatLean.PointEstimation.LinearModel.Canonical
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Least squares: unbiased optimality in the original coordinates

The canonical-form optimality statements are transported back to the original observation
vector. With the mean vector `ξ` constrained to a subspace `W` and the variance `σ²`
unknown, the least-squares estimator `ξ̂ = P_W y` supplies the optimal unbiased estimator of
every linear functional of `ξ`, and the residual sum of squares supplies the optimal
unbiased estimator of `σ²`:

* `linearModelFull W` — the model with *both* `ξ ∈ W` and `σ² > 0` unknown;
* `inner_lse_eq_inner_starProjection` — `⟪γ, ξ̂⟫ = ⟪P_W γ, y⟫`, the identity that makes the
  least-squares functional a linear statistic;
* `isUMVU_lse_functional` — `y ↦ ⟪γ, ξ̂(y)⟫` is UMVU for `ξ ↦ ⟪γ, ξ⟫`;
* `isUMVU_residualSumSq` — `‖y − ξ̂(y)‖² / (n − dim W)` is UMVU for `σ²`;
* `isUMVU_linear_functional_of_mean` — transfer of the optimality to any parametrization
  whose coordinates are linear functions of the mean vector (the mechanism behind the
  regression forms, both of full rank and of deficient rank with side conditions).

**Reference.** Classical least-squares theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* *Estimand normalization.* The estimand is stated for `γ ∈ W`. This is no restriction:
  for `ξ ∈ W` one has `⟪γ, ξ⟫ = ⟪P_W γ, ξ⟫` and `⟪γ, ξ̂⟫ = ⟪P_W γ, ξ̂⟫`, so a general
  coefficient vector is replaced by its projection without changing either the estimand or
  the estimator.
* The intended proof route is the classical one: an orthogonal basis adapted to `W` carries
  `linearModelFull W` to `canonicalModel`, under which `⟪γ, ξ̂⟫` becomes a linear
  combination of the signal block and `‖y − ξ̂‖²` becomes the residual sum of squares; the
  conclusions are then the canonical-model statements pulled back.
* `n − dim W` is a real subtraction of casts (never truncated natural subtraction); the
  standing dimension condition `dim W < n` keeps it positive.

**Bibliographic comments.** Least squares and the optimality of its linear functionals are
due to C. F. Gauss (*Theoria combinationis observationum erroribus minimis obnoxiae*,
1821/1823) and A. A. Markov (*Wahrscheinlichkeitsrechnung*, Teubner, 1912); the
coordinate-free formulation used here follows W. Kruskal ("When are Gauss–Markov and least
squares estimators identical?" in *Essays in Probability and Statistics*, 1965),
H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear Statistical
Inference and Its Applications*, 2nd ed., Wiley, 1973). The minimum-variance property in
the normal model rests on E. L. Lehmann and H. Scheffé ("Completeness, similar regions,
and unbiased estimation," *Sankhyā* **10** (1950), 305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {n : ℕ}

/-- The **normal linear model with unknown variance**: the mean vector ranges over the
subspace `W` and the common variance ranges over the positive reals, both unknown. -/
noncomputable def linearModelFull (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (p : ↥W × PosVar) : Measure (EuclideanSpace ℝ (Fin n)) :=
  linearModel W p.2.1 p.1

/-- The least-squares functional is a **linear statistic**: `⟪γ, P_W y⟫ = ⟪P_W γ, y⟫`
(self-adjointness of the orthogonal projection). -/
theorem inner_lse_eq_inner_starProjection (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection] (γ y : EuclideanSpace ℝ (Fin n)) :
    ⟪γ, lse W y⟫_ℝ = ⟪W.starProjection γ, y⟫_ℝ := by
  show ⟪γ, W.starProjection y⟫_ℝ = ⟪W.starProjection γ, y⟫_ℝ
  rw [← Submodule.inner_starProjection_left_eq_right]

/-- **Optimality of the least-squares functional**: with the mean vector constrained to `W`
and the variance unknown, `y ↦ ⟪γ, ξ̂(y)⟫` is the UMVU estimator of `ξ ↦ ⟪γ, ξ⟫`. -/
theorem isUMVU_lse_functional (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model, without which the variance is not estimable
    (hW : Module.finrank ℝ W < n)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional, taken
    -- inside the mean subspace (see the estimand-normalization note above)
    {γ : EuclideanSpace ℝ (Fin n)} (hγ : γ ∈ W) :
    IsUMVU (linearModelFull W) (fun p => ⟪γ, (p.1 : EuclideanSpace ℝ (Fin n))⟫_ℝ)
      (fun y => ⟪γ, lse W y⟫_ℝ) := by
  -- DEFERRAL-ELIGIBLE (named planned debt: `stdGaussian_eq_map_pi_orthonormalBasis`).
  -- The classical proof rotates `linearModelFull W` onto `canonicalModel` by an orthonormal
  -- basis adapted to `W` (its first `dim W` vectors span `W`), under which `⟪γ, ξ̂⟫` becomes
  -- a linear combination of the signal block (`isUMVU_linear_combination` in `Canonical`).
  -- The missing infrastructure is the isometry-invariance of the product-Gaussian vector,
  -- `(gaussianVector ξ σ²).map L = gaussianVector (L ξ) σ²` for an orthogonal `L`, together
  -- with an `IsUMVU`-transport lemma along a measurable equivalence of the sample space —
  -- a self-contained multi-lemma development independent of the canonical-model results,
  -- which are all proved (`Canonical.lean`, 0-sorry). No result in this area consumes it.
  sorry

/-- **Optimality of the residual variance estimator**: `‖y − ξ̂(y)‖²/(n − dim W)` is the
UMVU estimator of `σ²`. -/
theorem isUMVU_residualSumSq (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n) :
    IsUMVU (linearModelFull W) (fun p => (p.2.1 : ℝ))
      (fun y => residualSumSq W y / ((n : ℝ) - (Module.finrank ℝ W : ℝ))) := by
  -- DEFERRAL-ELIGIBLE (named planned debt: `stdGaussian_eq_map_pi_orthonormalBasis`).
  -- Under the same adapted-orthonormal-basis rotation as `isUMVU_lse_functional`, the
  -- residual sum of squares `‖y − ξ̂‖²` becomes the canonical residual sum of squares and
  -- `n − dim W` becomes the residual dimension `m`, reducing the claim to
  -- `isUMVU_residual_variance` (proved, `Canonical.lean`). Blocked on the same missing
  -- Gaussian isometry-invariance + `IsUMVU`-transport development.
  sorry

/-- **Transfer of optimality along a linear reparametrization**: if an estimand `T` agrees
on the mean subspace with a linear functional of the mean vector, then evaluating `T` at
the least-squares estimator gives the UMVU estimator of `T(ξ)`.

This is the mechanism by which the optimality statements extend from the mean vector to
regression coefficients: coefficients defined by a design of full row rank, and
coefficients defined by a deficient-rank design together with identifying side conditions,
are in both cases linear functions of the mean vector. -/
theorem isUMVU_linear_functional_of_mean (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n)
    (T : EuclideanSpace ℝ (Fin n) → ℝ) {γ : EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: on the mean subspace the estimand is the linear functional `⟪γ, ·⟫`;
    -- this is what the identification of a regression parametrization supplies
    (hT : ∀ ζ ∈ W, T ζ = ⟪γ, ζ⟫_ℝ) :
    IsUMVU (linearModelFull W) (fun p => T (p.1 : EuclideanSpace ℝ (Fin n)))
      (fun y => T (lse W y)) := by
  -- On the mean subspace, `T` agrees with the inner product against the *projected* vector
  -- `P_W γ ∈ W`; the statement is then a relabelling of `isUMVU_lse_functional`.
  have hkey : ∀ ζ ∈ W, T ζ = ⟪W.starProjection γ, ζ⟫_ℝ := by
    intro ζ hζ
    rw [hT ζ hζ, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hζ]
  have hbase := isUMVU_lse_functional W hW (γ := W.starProjection γ) (W.starProjection_apply_mem γ)
  have hg : (fun p : ↥W × PosVar => T (p.1 : EuclideanSpace ℝ (Fin n)))
      = fun p => ⟪W.starProjection γ, (p.1 : EuclideanSpace ℝ (Fin n))⟫_ℝ := by
    funext p; exact hkey _ p.1.2
  have hδ : (fun y => T (lse W y)) = fun y => ⟪W.starProjection γ, lse W y⟫_ℝ := by
    funext y; exact hkey _ (W.starProjection_apply_mem y)
  rw [hg, hδ]; exact hbase

end StatLean.PointEstimation
