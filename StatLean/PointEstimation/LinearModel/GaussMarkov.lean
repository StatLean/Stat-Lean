import StatLean.PointEstimation.LinearModel.LeastSquares
import StatLean.PointEstimation.LinearModel.Equivariant
import Mathlib.Probability.Moments.Covariance

/-!
# The Gauss–Markov theorem: least squares among linear estimators

Dropping normality *and* independence, and retaining only the first two moments — the mean
vector lies in the subspace `W` and the coordinates are uncorrelated with common variance
`σ²` — the least-squares functional `y ↦ ⟪γ, P_W y⟫` still minimizes the variance among all
linear estimators unbiased throughout `W`, and it is the *only* one that does so:

* `integral_inner_lse` — the least-squares functional is unbiased under the moment
  assumptions alone;
* `gauss_markov` — its variance does not exceed that of any competing linear unbiased
  estimator `y ↦ ⟪c, y⟫`;
* `blue_lse` — the best linear unbiased estimator is unique: a minimizing coefficient
  vector must be `P_W γ`;
* `isSubspaceEquivariant_inner_iff` — for linear estimators, equivariance under
  translations by `W` is exactly unbiasedness throughout `W`;
* `isMRE_lse_among_linear_equivariant` — consequently, under squared error the
  least-squares functional is minimum risk equivariant among linear equivariant estimators.

**Reference.** Classical least-squares optimality among linear unbiased estimators;
original sources in the bibliographic comments below.

**Proof formalization notes.**
* *Moments only.* The unknown law is a single probability measure `P` on the observation
  space constrained by mean and covariance hypotheses; no dominatedness, no independence,
  no family indexed by a parameter. The parameter enters only through the vector `ξ` named
  in the mean hypothesis.
* *Junk-value discipline.* Mathlib's `covariance` and `variance` return junk off `L²`, and
  Bochner integrals return junk off `L¹`; the integrability and square-integrability
  hypotheses — both part of the classical assumption that the coordinates have mean `ξᵢ`
  and finite variance `σ²` — are therefore carried explicitly, each statement asking only
  for the one it needs.
* *Where the hypotheses are used.* The variance comparison needs only the second-moment
  structure and the competitor's unbiasedness relation `⟪c, ζ⟫ = ⟪γ, ζ⟫` on `W`; the mean
  hypotheses are used exactly for the unbiasedness statement and for the squared-error
  (risk) form. They are kept apart for that reason instead of being bundled.
* The intended proof of the variance comparison is the classical one: unbiasedness on `W`
  says `P_W c = P_W γ`, whence `‖c‖² = ‖P_W γ‖² + ‖c − P_W c‖²`, and both variances are
  `σ²` times the respective squared norms; uniqueness is the equality case.
* *Imports.* Although the statements assume no normality, this file sits above the normal
  theory: the classical argument derives the comparison from the normal-model optimality
  (variances of linear statistics depend on the first two moments only), and the
  equivariance predicate is the one already fixed for the normal model rather than a second
  copy of it.

**Bibliographic comments.** The theorem is due to C. F. Gauss (*Theoria combinationis
observationum erroribus minimis obnoxiae*, 1821/1823), with the formulation for linear
unbiased estimators associated with A. A. Markov (*Wahrscheinlichkeitsrechnung*, Teubner,
1912); see W. Kruskal ("When are Gauss–Markov and least squares estimators identical?" in
*Essays in Probability and Statistics*, 1965) for the coordinate-free treatment, and
H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear Statistical
Inference and Its Applications*, 2nd ed., Wiley, 1973) for the standard developments and
extensions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {n : ℕ}

/-- **Unbiasedness of the least-squares functional under the moment assumptions**: if the
mean vector lies in `W`, then `y ↦ ⟪γ, P_W y⟫` has mean `⟪γ, ξ⟫`. -/
theorem integral_inner_lse {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {γ ξ : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: the mean vector is constrained to the mean subspace
    (hξ : ξ ∈ W)
    -- USER-INPUT: first moments of the observation
    (hmean : ∀ i, ∫ y, y i ∂P = ξ i)
    -- USER-INPUT: integrable coordinates (the first moments exist; Bochner integrals are
    -- junk-valued off `L¹`, so this cannot be left implicit in `hmean`)
    (hint : ∀ i, Integrable (fun y => y i) P) :
    ∫ y, ⟪γ, lse W y⟫_ℝ ∂P = ⟪γ, ξ⟫_ℝ := by
  sorry

/-- **Gauss–Markov**: among the linear estimators unbiased throughout the mean subspace,
the least-squares functional has the smallest variance. -/
theorem gauss_markov {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {σ2 : ℝ} {γ c : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: uncorrelated coordinates with common variance σ² (the second-moment
    -- assumption; neither normality nor independence is assumed)
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    -- USER-INPUT: square-integrable coordinates (finite second moments, part of the
    -- moment assumptions)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P)
    -- USER-INPUT: the competing linear estimator is unbiased throughout the mean subspace
    (hc : ∀ ζ ∈ W, ⟪c, ζ⟫_ℝ = ⟪γ, ζ⟫_ℝ) :
    variance (fun y => ⟪γ, lse W y⟫_ℝ) P ≤ variance (fun y => ⟪c, y⟫_ℝ) P := by
  sorry

/-- **Uniqueness of the best linear unbiased estimator**: a linear estimator unbiased
throughout the mean subspace whose variance is minimal has coefficient vector `P_W γ`, that
is, it *is* the least-squares functional. -/
theorem blue_lse {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {σ2 : ℝ} {γ c : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: nondegenerate observation; with σ² = 0 every coefficient vector ties
    (hσ2 : 0 < σ2)
    -- USER-INPUT: uncorrelated coordinates with common variance σ²
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    -- USER-INPUT: square-integrable coordinates (finite second moments)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P)
    -- USER-INPUT: the linear estimator is unbiased throughout the mean subspace
    (hc : ∀ ζ ∈ W, ⟪c, ζ⟫_ℝ = ⟪γ, ζ⟫_ℝ)
    -- LEAN-ONLY: the competitor attains the minimum of the previous theorem; this is the
    -- equality case, not an extra modelling assumption
    (hbest : variance (fun y => ⟪c, y⟫_ℝ) P ≤ variance (fun y => ⟪γ, lse W y⟫_ℝ) P) :
    c = W.starProjection γ := by
  sorry

/-- For a **linear** estimator, equivariance under translations by the mean subspace is the
same as unbiasedness throughout the mean subspace. -/
theorem isSubspaceEquivariant_inner_iff (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (γ c : EuclideanSpace ℝ (Fin n)) :
    IsSubspaceEquivariant W γ (fun y => ⟪c, y⟫_ℝ) ↔ ∀ b ∈ W, ⟪c, b⟫_ℝ = ⟪γ, b⟫_ℝ := by
  sorry

/-- Under squared error, the least-squares functional is minimum risk equivariant among the
**linear** equivariant estimators, under the moment assumptions alone. -/
theorem isMRE_lse_among_linear_equivariant {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [W.HasOrthogonalProjection] {σ2 : ℝ} {γ c ξ : EuclideanSpace ℝ (Fin n)}
    {P : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure P]
    -- USER-INPUT: the mean vector is constrained to the mean subspace
    (hξ : ξ ∈ W)
    -- USER-INPUT: first moments of the observation
    (hmean : ∀ i, ∫ y, y i ∂P = ξ i)
    -- USER-INPUT: uncorrelated coordinates with common variance σ²
    (hcov : ∀ i j, covariance (fun y => y i) (fun y => y j) P = if i = j then σ2 else 0)
    -- USER-INPUT: square-integrable coordinates (finite second moments)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 P)
    -- USER-INPUT: the competing linear estimator is equivariant under translations by the
    -- mean subspace
    (hequiv : IsSubspaceEquivariant W γ (fun y => ⟪c, y⟫_ℝ)) :
    ∫ y, (⟪γ, lse W y⟫_ℝ - ⟪γ, ξ⟫_ℝ) ^ 2 ∂P ≤ ∫ y, (⟪c, y⟫_ℝ - ⟪γ, ξ⟫_ℝ) ^ 2 ∂P := by
  sorry

end StatLean.PointEstimation
