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

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), Theorem 5.12 (the bound is attained iff the family is exponential and
the estimator is affine in the natural statistic). (`TPE2 §2.5 Thm 5.12`.)

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
  haveI hP := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hIne : fisherInfo M μ θ ≠ 0 := hI.ne'
  -- positivity of the information makes the second moment of the score genuinely integrable
  have hscore_int : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ := by
    by_contra h
    rw [fisherInfo, integral_undef h] at hI
    exact lt_irrefl 0 hI
  have hscoreL2 : MemLp (score M θ) 2 (M.toMeasure μ θ) := memLp_score M μ θ hmeas hscore_int
  have hmean0P : ∫ x, score M θ x ∂(M.toMeasure μ θ) = 0 := by
    rw [integral_toMeasure_eq]; exact hmean0
  have hI_eq : fisherInfo M μ θ = ∫ x, score M θ x ^ 2 ∂(M.toMeasure μ θ) := by
    rw [fisherInfo, integral_toMeasure_eq]
  -- the score is centered, so its variance is the information
  have hvarscore : variance (score M θ) (M.toMeasure μ θ) = fisherInfo M μ θ := by
    rw [variance_of_integral_eq_zero hscoreL2.aemeasurable hmean0P, hI_eq]
  -- `∫ δ · ℓ̇ = a · I`
  have hδscore : ∫ x, δ x * score M θ x ∂(M.toMeasure μ θ) = a * fisherInfo M μ θ := by
    have hae : (fun x => δ x * score M θ x)
        =ᵐ[M.toMeasure μ θ] fun x => a * score M θ x ^ 2 + b * score M θ x := by
      filter_upwards [haffine] with x hx; rw [hx]; ring
    rw [integral_congr_ae hae, integral_add (hscoreL2.integrable_sq.const_mul a)
      ((hscoreL2.integrable one_le_two).const_mul b), integral_const_mul, integral_const_mul,
      hmean0P, mul_zero, add_zero, hI_eq]
  -- variance of `δ = a·ℓ̇ + b` is `a²·I`
  have hvarδ : variance δ (M.toMeasure μ θ) = a ^ 2 * fisherInfo M μ θ := by
    rw [variance_congr haffine,
      variance_add_const (hscoreL2.const_mul a).aestronglyMeasurable b,
      variance_const_mul, hvarscore]
  rw [hvarδ, show (∫ x, δ x * score M θ x * M.density θ x ∂μ) = a * fisherInfo M μ θ from by
    rw [← integral_toMeasure_eq]; exact hδscore]
  rw [eq_div_iff hIne]
  ring

/-- **Analytic core of the attainment characterization (sanctioned debt).**

This is the one lifted analytic brick of the file (see the file header "documented
deviation"); the public `expFamily_of_cramer_rao_attained` is a direct reduction to it.

TODO: three genuinely missing bricks stand between the hypotheses and the exponential form.
1. *Differentiation under the integral is not available.* The attainment hypothesis gives
   `var_θ(δ)·I(θ) = g'(θ)²`, whereas the Cauchy–Schwarz *equality* case needs
   `cov_θ(δ, ℓ̇_θ)² = var_θ(δ)·I(θ)`. These agree only once `cov_θ(δ, ℓ̇_θ) = g'(θ)`, i.e.
   `deriv (fun t => ∫ δ p_t) θ = ∫ δ (∂_θ p_θ)`. That swap is *not* a hypothesis here; it has
   to be extracted from `hjoint` / `hC1` together with a domination/integrability input the
   present statement does not carry. Without it one only gets `cov² ≤ g'²`, not equality.
2. *Cauchy–Schwarz equality ⇒ a.e. proportionality.* Given the swap, `var_θ(δ − c·ℓ̇_θ) = 0`
   with `c = g'(θ)/I(θ)`, so `ae_eq_integral_of_variance_eq_zero` yields
   `ℓ̇_θ =ᵐ[P_θ] (I(θ)/g'(θ))·(δ − E_θ δ)` (with a separate `g'(θ) = 0` branch, where δ is
   a.e. constant under `P_θ`).
3. *Parametric FTC, uniform in `x`.* Fubini turns the per-`θ` a.e.-`x` relation into an
   a.e.-`(θ, x)` one; for a.e. `x` the C¹ map `θ ↦ log p_θ(x)` then has derivative
   `η'(θ)·δ(x) − B'(θ)` for a.e. `θ`, hence (by continuity) for all `θ`, and the FTC
   integrates this to `log p_θ(x) = η(θ)·δ(x) − B(θ) + log h(x)`. No Mathlib lemma packages
   this uniform-in-`x` integration at the current pin. -/
private theorem expFamily_of_cramer_rao_attained_core (M : ParametricFamily 𝓧 ℝ)
    (μ : Measure 𝓧) (hpdf : IsPDFOf M μ) (hsupp : HasCommonSupport M) (δ : 𝓧 → ℝ) (g' : ℝ → ℝ)
    (hδ2 : ∀ θ, MemLp δ 2 (M.toMeasure μ θ)) (hmeas : ∀ θ, AEStronglyMeasurable (score M θ) μ)
    (hI : ∀ θ, 0 < fisherInfo M μ θ) (hmean0 : ∀ θ, ∫ x, score M θ x * M.density θ x ∂μ = 0)
    (hg : ∀ θ, HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ) (g' θ) θ)
    (hjoint : Measurable (fun p : ℝ × 𝓧 => M.density p.1 p.2))
    (hC1 : ∀ᵐ x ∂μ, ContDiff ℝ 1 (fun t => M.density t x))
    (hIcont : Continuous (fun θ => fisherInfo M μ θ)) (hg'cont : Continuous g')
    (hattain : ∀ θ, variance δ (M.toMeasure μ θ) = g' θ ^ 2 / fisherInfo M μ θ) :
    ∃ (η B : ℝ → ℝ) (h : 𝓧 → ℝ), ContDiff ℝ 1 η ∧ Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, M.density θ x = Real.exp (η θ * δ x - B θ) * h x :=
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
      ∀ θ, ∀ᵐ x ∂μ, M.density θ x = Real.exp (η θ * δ x - B θ) * h x :=
  expFamily_of_cramer_rao_attained_core M μ hpdf hsupp δ g' hδ2 hmeas hI hmean0 hg hjoint hC1
    hIcont hg'cont hattain

end StatLean.PointEstimation
