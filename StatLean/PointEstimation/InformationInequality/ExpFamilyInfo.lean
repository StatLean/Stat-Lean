import StatLean.PointEstimation.InformationInequality.Basic
import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Moments.Covariance

/-!
# The Fisher information of an exponential family

In canonical form the log-density of an exponential family is `⟨η, T(x)⟩ − A(η)`, so its
score in the natural parameter is `T(x) − ∇A(η)`: the natural statistic, centered. The
information is therefore the *curvature of the log-partition function*, equivalently the
covariance of the natural statistic:
$$ I(\eta) = A''(\eta) \quad (\text{one-dimensional}), \qquad
   I(\eta)_{ij} = \frac{\partial^2 A}{\partial\eta_i\,\partial\eta_j}(\eta)
               = \operatorname{cov}_\eta\bigl(T_i, T_j\bigr) \quad (s\text{-dimensional}). $$

Contents:
* `ExpFamily.toParametricFamily` — the canonical family read as a family of densities
  `exp(⟨η, T(x)⟩ − A(η))` with respect to the reference measure, so that the score and the
  information of this area apply to it;
* `fisherInfo_expFamily` — the one-dimensional identity `I(η) = A''(η)`;
* `infoMatrix_expFamily` — the information matrix is the covariance matrix of the natural
  statistic.

**Reference.** Classical computation of the Fisher information of an exponential family in
its natural parametrization. Original sources in the bibliographic comments below.

**Proof formalization notes.**
* Both statements are given in the *natural* parametrization, where the score is
  `T − ∇A` and the identities are clean. The mean-value parametrization `τ = ∇A(η)` — in
  which the information is the *inverse* of the covariance matrix of `T`, and in dimension
  one `I(τ) = 1 / var_θ(T)` — follows by the reparametrization rule for the information
  (`fisherInfo_reparam` and its matrix analogue), since the Jacobian of `η ↦ τ(η)` is that
  same covariance matrix. This is a deliberate change of presentation, not of content.
* Smoothness of `A` is not assumed: it is forced by membership of `η` in the *interior* of
  the natural parameter set, where the log-partition function is analytic. That single
  membership hypothesis is therefore the only regularity input, and differentiability
  statements about `A` are consequences (proved in the exponential-family smoothness file),
  not hypotheses here.
* The density presentation `exp(⟨η, T x⟩ − A(η))` relative to `base` agrees with the
  member measure built by exponential tilting; where the reference measure is the zero
  measure both sides of the identities degenerate to `0` and the statements remain true.
* The `s`-dimensional statement is phrased entrywise, with the covariance of the coordinate
  statistics under the member measure, which is the form consumed by the multiparameter
  information inequality.

**Bibliographic comments.** The identification of the information of an exponential family
with the curvature of its cumulant function goes back to R. A. Fisher ("Theory of
statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925), 700–725) and to the
characterizations of exponential families by G. Darmois ("Sur les lois de probabilité à
estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935), 1265–1266), B. O. Koopman
("On distributions admitting a sufficient statistic," *Trans. Amer. Math. Soc.* **39**
(1936), 399–409) and E. J. G. Pitman ("Sufficient statistics and intrinsic accuracy,"
*Proc. Camb. Phil. Soc.* **32** (1936), 567–579). The matrix form of the information, and
its role in the multiparameter bound, are due to C. R. Rao ("Information and the accuracy
attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.* **37**
(1945), 81–91); the convex-analytic treatment of the log-partition function is that of
L. D. Brown (*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9, 1986).
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [OpensMeasurableSpace V]

/-- The canonical exponential family **read as a family of densities**
`p_η(x) = exp(⟨η, T(x)⟩ − A(η))` relative to its reference measure, so that the score and
the Fisher information of this area apply to it directly. The densities are positive
everywhere, so the family trivially has a common support. -/
noncomputable def ExpFamily.toParametricFamily (E : ExpFamily 𝓧 V) : ParametricFamily 𝓧 V where
  density η x := Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)
  density_meas η := by
    have h : Continuous fun v : V => ⟪η, v⟫_ℝ := continuous_const.inner continuous_id
    exact ((h.measurable.comp E.stat_meas).sub measurable_const).exp
  density_nonneg _ _ := Real.exp_nonneg _

/-- **The information of a one-dimensional canonical exponential family is the curvature of
its log-partition function**: `I(η) = A''(η)`.

The score is the centered natural statistic `T − A'(η)`, so the information is the variance
of `T` under the member measure, which is the second derivative of `A`. In the mean-value
parametrization this becomes the reciprocal of that variance, by the reparametrization rule
for the information. -/
theorem fisherInfo_expFamily (E : ExpFamily 𝓧 ℝ) (η : ℝ)
    -- USER-INPUT: the natural parameter lies in the interior of the natural parameter set;
    -- the classical condition under which the log-partition function is smooth (and hence
    -- the only regularity input of the statement)
    (hη : η ∈ interior E.natSet) :
    fisherInfo E.toParametricFamily E.base η = deriv (deriv E.logPartition) η := by
  sorry

/-- **The information matrix of a canonical exponential family is the covariance matrix of
its natural statistic**: `I(η)_{ij} = cov_η(T_i, T_j)`, equivalently the Hessian of the
log-partition function.

In the mean-value parametrization the information matrix is the *inverse* of this
covariance matrix, by the matrix reparametrization rule. -/
theorem infoMatrix_expFamily {s : ℕ} (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (η : EuclideanSpace ℝ (Fin s))
    -- USER-INPUT: the natural parameter lies in the interior of the natural parameter set
    (hη : η ∈ interior E.natSet) (i j : Fin s) :
    infoMatrix E.toParametricFamily E.base η i j
      = covariance (fun x => E.stat x i) (fun x => E.stat x j) (E.P η) := by
  sorry

end StatLean.PointEstimation
