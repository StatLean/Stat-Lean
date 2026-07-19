import StatLean.PointEstimation.InformationInequality.Basic
import StatLean.PointEstimation.UMVU.Defs

/-!
# The information inequality (Cramér–Rao bound)

For a dominated family with a common support whose score has mean zero and positive
information, every square-integrable statistic `δ` whose expectation may be differentiated
under the integral sign satisfies
$$ \operatorname{var}_\theta(\delta) \;\ge\;
   \frac{\bigl(\tfrac{\partial}{\partial\theta} E_\theta \delta\bigr)^2}{I(\theta)} . $$
Writing `E_θ δ = g(θ) + b(θ)` for an estimand `g` and the bias `b` of `δ`, the same
inequality reads `var_θ(δ) ≥ (b'(θ) + g'(θ))² / I(θ)`: no unbiasedness is needed, the bias
simply enters through its derivative.

Contents:
* `cramer_rao` — the information inequality in the form with the derivative of the
  expectation supplied as data;
* `cramer_rao_of_deriv` — the bias form, for an estimator of a differentiable estimand
  which need not be unbiased.

**Reference.** Classical information (Cramér–Rao) inequality for a real parameter, in the
version whose regularity conditions are imposed on the estimator. Original sources in the
bibliographic comments below.

**Proof formalization notes.**
* The proof is the covariance inequality `var(δ) ≥ cov(δ, ψ)² / var(ψ)` (Cauchy–Schwarz
  for the centered variables) applied to `ψ = ℓ̇_θ`, the score: the mean-zero property turns
  `var(ψ)` into `I(θ)` and turns `cov(δ, ψ)` into `∫ δ · ∂_θ p_θ dμ`, which the
  differentiation-under-the-integral hypothesis identifies with `∂_θ E_θ δ`.
* The derivative of `t ↦ ∫ δ p_t dμ` is supplied as an explicit `HasDerivAt` datum together
  with the identification `hswap` of its value as `∫ δ ∂_θ p_θ dμ`; these are exactly the
  two classical conditions on the estimator. They are *conditions*, not consequences: the
  companion file `InformationInequality.DensityRegularity` discharges both from a
  dominated-difference-quotient condition on the family alone.
* The common-support condition is what lets the junk-safe score be traded for the density
  derivative (`score_mul_density_eq_deriv`); without it the two integrals
  `∫ δ ℓ̇_θ p_θ dμ` and `∫ δ ∂_θ p_θ dμ` differ by the contribution of the set where the
  density vanishes, and the inequality is false in general.
* The bound is written as `g'^2 / I(θ) ≤ var(δ)` rather than with the division on the
  larger side, so that the vanishing-information case falls back on Lean's `x / 0 = 0`
  convention harmlessly; the hypothesis `0 < I(θ)` is nonetheless kept, as in the classical
  statement.

**Bibliographic comments.** The inequality was obtained independently by C. R. Rao
("Information and the accuracy attainable in the estimation of statistical parameters,"
*Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér (*Mathematical Methods of
Statistics*, Princeton University Press, 1946, §32.3), with earlier forms in M. Fréchet
("Sur l'extension de certaines évaluations statistiques au cas de petits échantillons,"
*Rev. Inst. Int. Statist.* **11** (1943), 182–205) and G. Darmois ("Sur les limites de la
dispersion de certaines estimations," *Rev. Inst. Int. Statist.* **13** (1945), 9–15). The
underlying covariance inequality goes back to R. A. Fisher's information calculus
("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925), 700–725).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **The information inequality (Cramér–Rao bound).** For a dominated family with a
common support, mean-zero score and positive information, and for a square-integrable
statistic `δ` whose expectation `t ↦ E_t δ` is differentiable at `θ` with derivative `g'`
obtained by differentiating under the integral sign,
`(∂_θ E_θ δ)² / I(θ) ≤ var_θ(δ)`.

For an unbiased estimator of an estimand `g` this is the familiar `g'(θ)² / I(θ)`; the
biased case is `cramer_rao_of_deriv`. -/
theorem cramer_rao (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ) (δ : 𝓧 → ℝ) (g' : ℝ)
    -- LEAN-ONLY: measurability of the score, which is built from a `deriv` in the parameter
    -- and therefore carries no measurability in `x` by construction; it is a consequence of
    -- the family-side regularity used in `cramer_rao_of_density_regular`, and only in this
    -- estimator-side shape does it have to be supplied
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`; the first classical
    -- condition on the estimator
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: finiteness of the information as a Bochner integral, so that `fisherInfo`
    -- is the genuine second moment of the score rather than the junk value `0`; redundant
    -- given positivity of the information below, kept as an explicit datum of this shape
    (hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- USER-INPUT: the information is positive; classical standing assumption
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the expectation of the statistic is differentiable at `θ`; the second
    -- classical condition on the estimator
    (hdiff : HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ) g' θ)
    -- USER-INPUT: that derivative is obtained by differentiating under the integral sign
    (hswap : g' = ∫ x, δ x * deriv (fun t => M.density t x) θ ∂μ)
    -- USER-INPUT: the score has mean zero; classical regularity condition, implied by
    -- differentiation under the integral sign in the normalisation identity
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0) :
    g' ^ 2 / fisherInfo M μ θ ≤ variance δ (M.toMeasure μ θ) := by
  sorry

/-- **The information inequality with bias.** If `δ` estimates `g` with bias `b`, so that
`E_t δ = g(t) + b(t)`, and both `g` and `b` are differentiable at `θ`, then
`(b'(θ) + g'(θ))² / I(θ) ≤ var_θ(δ)`.

Unbiasedness is *not* assumed: for `b = 0` this is the bound `g'(θ)² / I(θ)` for unbiased
estimators, and in general the bias enters only through its derivative, so an estimator can
beat the unbiased bound only by having a nonconstant bias. -/
theorem cramer_rao_of_deriv (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ) (δ : 𝓧 → ℝ) (g b : ℝ → ℝ) (g' b' : ℝ)
    -- USER-INPUT: `b` is the bias of `δ` as an estimator of `g`
    (hbias : ∀ t, ∫ x, δ x * M.density t x ∂μ = g t + b t)
    -- USER-INPUT: the estimand is differentiable at `θ`
    (hg : HasDerivAt g g' θ)
    -- USER-INPUT: the bias is differentiable at `θ`
    (hb : HasDerivAt b b' θ)
    -- LEAN-ONLY: measurability of the score (see `cramer_rao`)
    (hmeas : AEStronglyMeasurable (score M θ) μ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ))
    -- LEAN-ONLY: finiteness of the information as a Bochner integral
    (hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- USER-INPUT: the information is positive; classical standing assumption
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the derivative of the expectation is obtained by differentiating under
    -- the integral sign
    (hswap : b' + g' = ∫ x, δ x * deriv (fun t => M.density t x) θ ∂μ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0) :
    (b' + g') ^ 2 / fisherInfo M μ θ ≤ variance δ (M.toMeasure μ θ) := by
  sorry

end StatLean.PointEstimation
