import StatLean.PointEstimation.InformationInequality.CramerRao
import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Attainment of the information bound: exponential families

The information inequality comes from Cauchy–Schwarz, so it is an equality exactly when the
statistic is an affine function of the score,
$$ \delta(x) = a\,\frac{\partial}{\partial\theta}\log p_\theta(x) + b, $$
with `a, b` allowed to depend on `θ`. If this happens *at every* parameter value with `a`
and `b` free of `x`, the family is forced to be an exponential family in which `δ` is the
natural statistic: the density takes the form `exp(η(θ) δ(x) − B(θ)) h(x)`.

Contents:
* `cramer_rao_attained_of_affine` — the easy direction: an affine function of the score
  attains the bound, with no regularity conditions on the family;
* `expFamily_of_cramer_rao_attained` — the converse: attainment at every parameter value
  forces the exponential form.

**Reference.** Classical characterization of equality in the information inequality: the
bound is attained if and only if the underlying family is a one-parameter exponential family
with the estimator as natural statistic. Original sources in the bibliographic comments
below.

**Proof formalization notes.**
* The easy direction is stated at a *single* parameter value and assumes nothing about the
  family beyond the mean-zero score and a positive, finite information at that value: it is
  the equality case of Cauchy–Schwarz, and the constants `a, b` may depend on `θ`. If they
  do depend on `θ`, the affine function of the score is not an estimator, and no estimator
  attains the bound — which is why the converse quantifies over all parameter values with
  one fixed `δ`.
* **Documented deviation.** The converse is proved under *more* regularity than the
  classical statement, which assumes only the common-support condition and a finite variance
  of `δ`: we additionally require joint measurability of `(θ, x) ↦ p_θ(x)`, continuous
  differentiability of `θ ↦ p_θ(x)` for almost every `x`, and continuity of `θ ↦ I(θ)` and
  of the derivative of `θ ↦ E_θ δ`. These are what make the pointwise equality case of
  Cauchy–Schwarz integrate to an ordinary differential equation for `log p_θ(x)` in `θ` that
  may be solved by the fundamental theorem of calculus, uniformly in `x`. The classical
  proof obtains the same conclusion by a measure-theoretic argument that avoids the
  continuity assumptions; we have not formalized that route, and the extra hypotheses are
  therefore a genuine strengthening of the assumptions, not a restatement.
* The conclusion carries measurability and non-negativity of the carrier `h`, so that the
  produced representation can be fed to the exponential-family constructor that absorbs a
  carrier into the reference measure.
* The classical statement also records the accompanying identities relating the natural
  parameter, the estimand and the information — the estimator equals `(g'(θ)/I(θ))` times
  the score plus `g(θ)`, and `I(θ) = η'(θ) g'(θ)`. They are consequences of the
  representation and of the easy direction, and are not part of this conclusion.

**Bibliographic comments.** That equality in the information inequality characterizes
exponential families with the estimator as natural statistic was observed already by
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér (*Mathematical
Methods of Statistics*, Princeton University Press, 1946, §32.3), in the spirit of the
characterizations of exponential families by G. Darmois ("Sur les lois de probabilité à
estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935), 1265–1266). Necessary and
sufficient conditions for attainment under weak regularity are due to R. A. Wijsman ("On the
attainment of the Cramér–Rao lower bound," *Ann. Statist.* **1** (1973), 538–542) and
V. Fabian and J. Hannan ("On the Cramér–Rao inequality," *Ann. Statist.* **5** (1977),
197–205).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Affine functions of the score attain the information bound.** If, at the parameter
value `θ`, the statistic is almost surely `a · ℓ̇_θ + b` for constants `a, b`, then its
variance equals the information bound `(E_θ[δ ℓ̇_θ])² / I(θ)`.

No regularity of the family is needed: this is the equality case of Cauchy–Schwarz, applied
to the centered score. The constants are allowed to depend on `θ` — in which case the affine
function is not an estimator and no estimator attains the bound. -/
theorem cramer_rao_attained_of_affine (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    (θ : ℝ) (δ : 𝓧 → ℝ) (a b : ℝ)
    -- LEAN-ONLY: measurability of the score, which is built from a `deriv` in the parameter
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the information is positive (and hence finite as a Bochner integral)
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- USER-INPUT: the statistic is an affine function of the score at `θ`
    (haffine : ∀ᵐ x ∂(M.toMeasure μ θ), δ x = a * score M θ x + b) :
    variance δ (M.toMeasure μ θ)
      = (∫ x, δ x * score M θ x * M.density θ x ∂μ) ^ 2 / fisherInfo M μ θ := by
  sorry

/-- **Attainment forces an exponential family.** If one statistic `δ` attains the
information bound at *every* parameter value, then the densities admit the exponential
representation `p_θ(x) = exp(η(θ) δ(x) − B(θ)) h(x)` with `η` continuously differentiable:
the family is a one-parameter exponential family with `δ` as its natural statistic.

This statement carries more regularity than the classical one — joint measurability of the
densities, continuous differentiability in the parameter almost everywhere, and continuity
of the information and of the derivative of the expectation of `δ`. See the deviation note
in the file header. -/
theorem expFamily_of_cramer_rao_attained (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (δ : 𝓧 → ℝ) (g' : ℝ → ℝ)
    -- USER-INPUT: the statistic has a finite second moment at every parameter value
    (hδ2 : ∀ θ, MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: measurability of the score at every parameter value
    (hmeas : ∀ θ, AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the information is positive at every parameter value
    (hI : ∀ θ, 0 < fisherInfo M μ θ)
    -- USER-INPUT: the score has mean zero at every parameter value
    (hmean0 : ∀ θ, ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- USER-INPUT: the expectation of the statistic is differentiable, with derivative `g'`
    (hg : ∀ θ, HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ) (g' θ) θ)
    -- USER-INPUT (extra regularity, documented deviation): the densities are jointly
    -- measurable in the parameter and the observation
    (hjoint : Measurable (fun p : ℝ × 𝓧 => M.density p.1 p.2))
    -- USER-INPUT (extra regularity, documented deviation): almost every parameter section
    -- of the density is continuously differentiable
    (hC1 : ∀ᵐ x ∂μ, ContDiff ℝ 1 (fun t => M.density t x))
    -- USER-INPUT (extra regularity, documented deviation): the information is continuous
    (hIcont : Continuous (fun θ => fisherInfo M μ θ))
    -- USER-INPUT (extra regularity, documented deviation): the derivative of the
    -- expectation of the statistic is continuous
    (hg'cont : Continuous g')
    -- USER-INPUT: the information bound is attained at every parameter value
    (hattain : ∀ θ, variance δ (M.toMeasure μ θ) = g' θ ^ 2 / fisherInfo M μ θ) :
    ∃ (η B : ℝ → ℝ) (h : 𝓧 → ℝ), ContDiff ℝ 1 η ∧ Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, M.density θ x = Real.exp (η θ * δ x - B θ) * h x := by
  sorry

end StatLean.PointEstimation
