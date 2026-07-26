import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The multivariate bootstrap: mean vectors and smooth functions of means

The mean of a law on the line is replaced by the mean **vector** of a law on `ℝᵏ`. Two
consequences follow. First, the root can be built from the vector by any norm, and the bootstrap
handles every norm at once — the analytic approximation would have to be redone for each.
Second, once mean vectors are available, so is every parameter obtained by applying a smooth map
to a vector of expectations, through the delta method.

This file contains:

* `covMatrix`, `meanVecSeqClass`, `meanVecRootLaw`, `normLimitCDF`, `normMeanRootCDF` — the
  multivariate carriers;
* `meanVec_root_tendsto` — the multivariate limit law along the class;
* `norm_root_cdf_tendsto`, `continuous_normLimitCDF` — the limit law of the norm of the root;
* `bootstrap_meanVec_consistent` — almost sure consistency of the bootstrap for the mean vector;
* `meanStatistic`, `bootstrapLaw` — the plug-in statistic and the resampling law;
* `smooth_function_of_means_tendsto` — the delta-method limit for smooth functions of means;
* `bootstrap_smooth_function_consistent` — almost sure bootstrap consistency for those
  functions, in the two forms stated for them: closeness of the resampled law to the sampling
  law, and uniform closeness of the distribution functions of the norm.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), Theorem 18.3.5 (the
multivariate bootstrap) and Theorem 18.3.6 (smooth functions of means), §18.3.3 (Further
Examples). (`TSH4 §18.3 Thm 18.3.5, Thm 18.3.6`.)

**Designed deviation (metric-free formulation).** Closeness of two laws on `ℝᵏ` is classically
expressed through a metric metrizing weak convergence (bounded-Lipschitz, Lévy–Prokhorov, …).
We keep the metric out of the statements: weak convergence is written as convergence of
integrals of bounded continuous functions, and the displays that the reference states in a
metric are rendered either in that form or — where the reference itself supplies a supremum over
a real argument — in the frozen `supCDFDist`. No metric on the space of measures is introduced.

**Deviation from the reference class (mean-vector convergence).** The reference defines the
multivariate class by weak convergence together with entrywise convergence of the covariance
matrices, and proves the limit law by reduction to the univariate mean case. That reduction
consumes convergence of the **mean vectors** as well: along a direction, the univariate class
requires the means to converge. We therefore include mean-vector convergence in
`meanVecSeqClass`. The empirical sequence satisfies it by the strong law, so no application is
weakened.

**Proof formalization notes.**
* Part (i) is the Cramér–Wold reduction of the multivariate limit to the univariate one: apply
  `mean_root_cdf_tendsto` in each direction and recombine. The multivariate central limit
  theorem in the repository (`ForMathlib/MultivariateCLT`) provides the recombination, and
  `multivariateGaussian` is the limit law.
* Part (ii) is the continuous mapping theorem for the norm: a norm is continuous everywhere, and
  the boundary spheres of a nondegenerate Gaussian are null, so the distribution function of the
  norm is continuous — recorded separately as `continuous_normLimitCDF`, since the almost sure
  part needs it to run the uniform (Polya) step.
* Part (iii) is the general sequence-class criterion applied to the empirical sequence, whose
  membership follows from the multivariate Glivenko–Cantelli theorem and the strong law.
* The norm is passed as data with the three defining hypotheses (subadditive, absolutely
  homogeneous, positive definite) rather than as a `NormedAddCommGroup` instance, because the
  statement quantifies over norms on a space that already carries its Euclidean one.
* Coordinates of `EuclideanSpace` are read through `WithLp.ofLp` and built through
  `WithLp.toLp`; the space is a structure over the underlying function type in this pin, so
  bare lambdas do not typecheck.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26); the multivariate theory to P. J. Bickel
and D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.* **9** (1981),
1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap," *Ann. Statist.* **9**
(1981), 1187–1195). Confidence sets for a multivariate distribution built from the bootstrap,
and the balancing of simultaneous intervals, are due to R. Beran ("Bootstrap methods in
statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30) and R. Beran and
P. W. Millar ("Confidence sets for a multivariate distribution," *Ann. Statist.* **14** (1986),
431–443); see also D. N. Politis, J. P. Romano and M. Wolf, *Subsampling*, Springer, 1999, and
P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer, 1992.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StatLean.HypothesisTesting

variable {Ω 𝓢 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓢] {k p q : ℕ}

/-! ## Carriers for the mean vector -/

/-- The **covariance matrix** of a law on `ℝᵏ`, entry by entry. -/
noncomputable def covMatrix (F : Measure (EuclideanSpace ℝ (Fin k))) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    cov[fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i,
        fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y j; F]

/-- The **sequence class for the mean-vector problem**: sequences of laws on `ℝᵏ` converging
weakly to `Q` — tested against bounded continuous functions — with mean vectors and covariance
matrices converging entrywise to those of `Q`. The `n = 0` entry is left unconstrained, as in
the univariate class. -/
def meanVecSeqClass (Q : Measure (EuclideanSpace ℝ (Fin k))) :
    Set (ℕ → Measure (EuclideanSpace ℝ (Fin k))) :=
  {F | (∀ n : ℕ, 0 < n → IsProbabilityMeasure (F n)) ∧
    (∀ n : ℕ, MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 (F n)) ∧
    (∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      Tendsto (fun n => ∫ y, f y ∂(F n)) atTop (𝓝 (∫ y, f y ∂Q))) ∧
    (∀ i : Fin k, Tendsto (fun n => ∫ y, WithLp.ofLp y i ∂(F n)) atTop
      (𝓝 (∫ y, WithLp.ofLp y i ∂Q))) ∧
    (∀ i j : Fin k, Tendsto (fun n => covMatrix (F n) i j) atTop (𝓝 (covMatrix Q i j)))}

/-- The **law of the centred and scaled sample mean vector** under `n` independent draws
from `F`. -/
noncomputable def meanVecRootLaw (F : Measure (EuclideanSpace ℝ (Fin k))) (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  (Measure.pi fun _ : Fin n => F).map
    fun y => Real.sqrt n • ((n : ℝ)⁻¹ • (∑ i, y i) - ∫ z, z ∂F)

/-- The **limiting distribution function of the norm** of a centred Gaussian vector with
covariance `S`, for the norm `nrm`. -/
noncomputable def normLimitCDF (S : Matrix (Fin k) (Fin k) ℝ)
    (nrm : EuclideanSpace ℝ (Fin k) → ℝ) (x : ℝ) : ℝ :=
  ((multivariateGaussian 0 S) {z | nrm z ≤ x}).toReal

/-- The **sampling distribution function of the norm** of the centred and scaled sample mean
vector under `n` independent draws from `F`. -/
noncomputable def normMeanRootCDF (F : Measure (EuclideanSpace ℝ (Fin k)))
    (nrm : EuclideanSpace ℝ (Fin k) → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((meanVecRootLaw F n) {z | nrm z ≤ x}).toReal

/-! ## The mean vector -/

section MeanVector

variable {Q : Measure (EuclideanSpace ℝ (Fin k))} {F : ℕ → Measure (EuclideanSpace ℝ (Fin k))}
  {nrm : EuclideanSpace ℝ (Fin k) → ℝ} {Pr : Measure Ω} {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}

/-- **Limit law of the mean vector along the class.**

Along every sequence of the mean-vector class, the law of the centred and scaled sample mean
vector converges weakly to the centred multivariate normal law with the limiting covariance
matrix. -/
theorem meanVec_root_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable, so its mean vector and covariance exist
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the sequence of laws belongs to the mean-vector class
    (hF : F ∈ meanVecSeqClass Q)
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, f z ∂(meanVecRootLaw (F n) n)) atTop
      (𝓝 (∫ z, f z ∂(multivariateGaussian 0 (covMatrix Q)))) := by
  -- TODO (triangular-array multivariate CLT, drifting row law — Vitali gap). Cramér–Wold: for
  -- each direction `t`, `⟪t, ·⟫` of the root is the univariate standardised sum of the i.i.d.
  -- draws `⟪t, X_{n,i}⟫`, `X_{n,i} ~ F n`. Realise on `Π n, (Fin n → ℝᵏ)`, reduce to
  -- `ForMathlib.LindebergCLT.lindeberg_clt`, and identify the limit `charFun` with
  -- `multivariateGaussian 0 (covMatrix Q)` via `charFun_multivariateGaussian` + Lévy
  -- (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`), exactly as the proven fixed-law brick
  -- `ProbabilityTheory.tendstoInDistribution_multivariate_clt` does. The ONE genuinely missing
  -- step is the Lindeberg condition for the *drifting* rows: it follows from
  -- `Var[⟪t,·⟫; F n] → Var[⟪t,·⟫; Q]` plus weak convergence via *uniform square-integrability*
  -- (Lehmann–Romano Lemma 18.3.1 / Vitali): `Xₙ ⇒ X` with `E Xₙ² → E X² < ∞` forces `{Xₙ²}`
  -- uniformly integrable. This Vitali-type upgrade is absent from Mathlib v4.29.1 (the same gap
  -- recorded on `mean_root_cdf_tendsto`). Being a weak-convergence (bounded-continuous) target,
  -- this needs NO portmanteau CDF-inversion, unlike its univariate sibling.
  sorry

/-- **The limiting distribution function of the norm is continuous.**

If the limiting covariance matrix has a nonzero entry, the norm of the Gaussian limit has no
atoms: the spheres of a norm are boundaries of convex sets and hence null for the limit law. -/
theorem continuous_normLimitCDF
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: the limiting covariance is not identically zero, so the limit is nondegenerate
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0) :
    Continuous (normLimitCDF (covMatrix Q) nrm) := by
  -- TODO (norm-CDF of a possibly-degenerate Gaussian — two missing bricks). Continuity of the
  -- monotone `x ↦ (μ {nrm ≤ x}).toReal` (μ := multivariateGaussian 0 (covMatrix Q)) is
  -- equivalent to `μ {nrm z = x} = 0` for every `x`. Intended clean route, degeneracy-robust:
  -- `μ = (toEuclideanCLM (CFC.sqrt S))_* stdGaussian` (the DEFINITION), so
  -- `μ {nrm z = x} = stdGaussian {z | g z = x}` with `g := nrm ∘ √S` a *seminorm*
  -- (subadditive+absolutely homogeneous from `hnrm_add`/`hnrm_smul`; possibly degenerate). For
  -- `x > 0`, `{g = x} ⊆ frontier {g ≤ x}` (a convex set), null by `Convex.addHaar_frontier`;
  -- for `x = 0`, `{g = 0} = ker √S`, a proper subspace (hence hyperplane-null) since `√S ≠ 0`;
  -- for `x < 0`, `{g = x} = ∅`. Two bricks are missing in Mathlib v4.29.1:
  --   (1) `stdGaussian ≪ volume` (to transfer the `volume`-null frontier to the Gaussian): NOT
  --       in Mathlib; buildable from `Measure.pi (gaussianReal 0 1) ≪ volume` (no `Measure.pi`
  --       absolute-continuity lemma exists yet) transported through the orthonormal-basis iso
  --       `∑ xᵢ • bᵢ`, but the `WithLp`/`EuclideanSpace` volume-preservation is heavy;
  --   (2) `(covMatrix Q).PosSemidef`, needed to get `√S ≠ 0` from `hS : S ≠ 0`. It is NOT a
  --       hypothesis here (the frozen signature lacks `hQ2`), and `covMatrix Q` is provably PSD
  --       only under `MemLp id 2 Q` (via `covarianceBilin_apply_eq_cov` +
  --       `isPosSemidef_covarianceBilin`). Without PSD, `multivariateGaussian 0 S = dirac 0`
  --       and the CDF jumps at `0`; so the statement is true exactly under square-integrability.
  sorry

/-- **Limit law of the norm of the root along the class.**

Along every sequence of the mean-vector class, the sampling distribution function of the norm of
the centred and scaled sample mean vector converges to the distribution function of the norm of
the Gaussian limit — for **every** norm on `ℝᵏ`. -/
theorem norm_root_cdf_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the sequence of laws belongs to the mean-vector class
    (hF : F ∈ meanVecSeqClass Q)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: nondegeneracy of the limiting covariance
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0)
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (x : ℝ) :
    Tendsto (fun n => normMeanRootCDF (F n) nrm n x) atTop
      (𝓝 (normLimitCDF (covMatrix Q) nrm x)) := by
  -- TODO (continuous mapping for the norm — portmanteau on top of the two blocked cores).
  -- From `meanVec_root_tendsto` the laws `meanVecRootLaw (F n) n` converge weakly (against
  -- bounded continuous test functions) to `multivariateGaussian 0 (covMatrix Q)`; promote to
  -- `ProbabilityMeasure` weak convergence and apply
  -- `MeasureTheory.tendsto_measure_of_null_frontier` to the sublevel set `{z | nrm z ≤ x}`,
  -- whose frontier `⊆ {nrm z = x}` is Gaussian-null. That null-frontier fact is exactly the
  -- analytic core of `continuous_normLimitCDF`, so this target is blocked transitively on both
  -- (a) `meanVec_root_tendsto` (Vitali/Lindeberg gap) and (b) the norm-sphere nullity of the
  -- limit Gaussian (`stdGaussian ≪ volume` + `covMatrix Q` PosSemidef gaps).
  sorry

/-- **Consistency of the multivariate bootstrap.**

For an independent identically distributed sample from a square-integrable law on `ℝᵏ` with a
nondegenerate covariance, the bootstrap sampling distribution of the norm of the root is
uniformly close to the true one, almost surely, for every norm. -/
theorem bootstrap_meanVec_consistent [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: nondegeneracy of the covariance
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (normMeanRootCDF Q nrm n)
      (normMeanRootCDF (empiricalMeasure fun i : Fin n => X i ω) nrm n)) atTop (𝓝 0) := by
  -- TODO (bootstrap consistency assembly — needs multivariate empirical membership + the blocked
  -- norm cores). Structurally this is `tendsto_supCDFDist_bootstrap` (or the direct triangle
  -- squeeze of `bootstrap_mean_consistent`) with `J n F := normMeanRootCDF F nrm n`,
  -- `Jlim := normLimitCDF (covMatrix Q) nrm`, and `Phat n ω := empiricalMeasure (X · ω)`. The
  -- pointwise convergence along the class is `norm_root_cdf_tendsto`, continuity of the limit is
  -- `continuous_normLimitCDF`. The remaining stochastic input — a.s. membership of the empirical
  -- sequence in `meanVecSeqClass Q` — needs the *weak-convergence* clause `∀ f : ℝᵏ →ᵇ ℝ,
  -- ∫ f dP̂ₙ → ∫ f dQ` a.s., i.e. almost-sure weak convergence of empirical measures for ALL
  -- bounded continuous `f` (multivariate Glivenko–Cantelli / Varadarajan). Mathlib v4.29.1 has
  -- no `empiricalMeasure` weak-convergence theorem (the univariate `empirical_mem_meanSeqClass`
  -- dodges it with a rational CDF sandwich, unavailable for the BCF clause here). Blocked on that
  -- plus `norm_root_cdf_tendsto` and `continuous_normLimitCDF`.
  sorry

end MeanVector

/-! ## Smooth functions of means -/

/-- The **vector of sample means** of the coordinate functions `h`. -/
noncomputable def meanStatistic {n : ℕ} (h : Fin p → 𝓢 → ℝ) (z : Fin n → 𝓢) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun j => (n : ℝ)⁻¹ * (∑ i, h j (z i))

/-- The **bootstrap resampling law**: `n` independent draws from the empirical measure of the
observed sample. -/
noncomputable def bootstrapLaw {n : ℕ} (x : Fin n → 𝓢) : Measure (Fin n → 𝓢) :=
  Measure.pi fun _ : Fin n => empiricalMeasure x

section SmoothFunctions

variable {P : Measure 𝓢} {Pr : Measure Ω} {X : ℕ → Ω → 𝓢} {h : Fin p → 𝓢 → ℝ}
  {f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q)}
  {Df : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin q)} {D : Matrix (Fin q) (Fin p) ℝ}
  {covH : Matrix (Fin p) (Fin p) ℝ} {nrm : EuclideanSpace ℝ (Fin q) → ℝ}

/-- **Delta-method limit for a smooth function of means.**

Let each coordinate of the parameter be an expectation `∫ h j dP` estimated by the corresponding
sample mean, and let `f` be differentiable at the parameter with a nonzero differential that is
continuous there. Then the centred and scaled image `n^{1/2}(f(θ̂ₙ) − f(θ))` converges weakly to
the centred multivariate normal law with covariance `D Σ Dᵀ`, where `Σ` is the covariance matrix
of the vector of coordinate functions and `D` is the matrix of the differential. -/
theorem smooth_function_of_means_tendsto [IsProbabilityMeasure P]
    -- USER-INPUT: the coordinate functions are measurable and square-integrable
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P)
    -- USER-INPUT: `f` is differentiable at the parameter with differential `Df`
    (hf : HasFDerivAt f Df (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- USER-INPUT: the differential does not vanish
    (hDf_ne : Df ≠ 0)
    -- USER-INPUT: `f` is differentiable near the parameter; half of the reference's
    -- "nonzero continuous differential" condition
    (hf_nhds : ∀ᶠ y in 𝓝 (WithLp.toLp (2 : ℝ≥0∞) fun j => ∫ s, h j s ∂P),
      DifferentiableAt ℝ f y)
    -- USER-INPUT: the differential is continuous at the parameter; the other half
    (hf_cont : ContinuousAt (fderiv ℝ f) (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- USER-INPUT: `D` is the matrix of the differential
    (hD : ∀ v, Df v = WithLp.toLp 2 (D.mulVec (WithLp.ofLp v)))
    -- USER-INPUT: `covH` is the covariance matrix of the vector of coordinate functions
    (hcovH : ∀ i j, covH i j = cov[h i, h j; P])
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (φ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ z, φ z ∂((Measure.pi fun _ : Fin n => P).map
        fun w => Real.sqrt n • (f (meanStatistic h w) -
          f (WithLp.toLp 2 fun j => ∫ s, h j s ∂P)))) atTop
      (𝓝 (∫ z, φ z ∂(multivariateGaussian 0 (D * covH * D.transpose)))) := by
  -- TODO (delta method — Slutsky/Taylor bricks absent). The mean statistic `meanStatistic h w`
  -- is the sample mean of the i.i.d. vector `(h j (·))ⱼ`, so the PROVEN fixed-law
  -- `ProbabilityTheory.tendstoInDistribution_multivariate_clt` gives
  -- `√n (θ̂ₙ − θ) ⇒ N(0, covH)` with `θ := (∫ h j dP)ⱼ`. First-order Taylor at `θ`:
  -- `√n (f(θ̂ₙ) − f(θ)) = Df (√n (θ̂ₙ − θ)) + √n · o(‖θ̂ₙ − θ‖)`, where the remainder → 0 in
  -- probability (`θ̂ₙ − θ = O_p(n^{-1/2})` and `hf`/`hf_nhds`/`hf_cont`). Then Slutsky +
  -- continuous mapping push `Df (N(0, covH))` to the limit; `isGaussian_map` identifies the
  -- image as Gaussian and `hD` gives covariance `D covH Dᵀ`. Missing from Mathlib v4.29.1: the
  -- Slutsky theorem for a vanishing (o_P) additive remainder attached to a weakly-convergent
  -- sequence, i.e. the analytic engine of the multivariate delta method. Blocked there.
  sorry

/-- **Bootstrap consistency for a smooth function of means, resampled-law form.**

Almost surely, the law of the resampled and recentred image is asymptotically indistinguishable
from the sampling law of the centred and scaled image, tested against bounded continuous
functions. -/
theorem bootstrap_smooth_function_law_consistent [IsProbabilityMeasure P] [IsProbabilityMeasure Pr]
    -- LEAN-ONLY: the observations are measurable
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `P`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) P Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: the coordinate functions are measurable and square-integrable
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P)
    -- USER-INPUT: `f` is differentiable at the parameter with nonzero continuous differential
    (hf : HasFDerivAt f Df (WithLp.toLp 2 fun j => ∫ s, h j s ∂P)) (hDf_ne : Df ≠ 0)
    -- USER-INPUT: the differential is continuous at the parameter
    (hf_cont : ContinuousAt (fderiv ℝ f) (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- LEAN-ONLY: argument quantified by the conclusion, not a hypothesis
    (φ : EuclideanSpace ℝ (Fin q) →ᵇ ℝ) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ =>
        ∫ z, φ z ∂((Measure.pi fun _ : Fin n => P).map
          fun w => Real.sqrt n • (f (meanStatistic h w) -
            f (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))) -
        ∫ z, φ z ∂((bootstrapLaw fun i : Fin n => X i ω).map
          fun w => Real.sqrt n • (f (meanStatistic h w) -
            f (meanStatistic h fun i : Fin n => X i ω)))) atTop (𝓝 0) := by
  -- TODO (bootstrap delta method, resampled-law form). Both integrals converge to
  -- `∫ φ d(multivariateGaussian 0 (D covH Dᵀ))`: the sampling-law term by
  -- `smooth_function_of_means_tendsto`, the resampled term by its bootstrap analogue (the same
  -- delta method applied to `n` i.i.d. draws from the empirical measure, recentred at the sample
  -- mean statistic). Subtracting gives `→ 0`. Blocked on `smooth_function_of_means_tendsto`
  -- (delta-method Slutsky brick, absent) together with a.s. convergence of the bootstrap CLT for
  -- the resampled means — i.e. the empirical-measure weak-convergence gap already flagged on
  -- `bootstrap_meanVec_consistent`.
  sorry

/-- **Bootstrap consistency for a smooth function of means, uniform distribution-function form.**

Almost surely, the sampling distribution function of the norm of the estimation error is
uniformly approximated by its resampled counterpart. Taking the maximum norm on the image space,
this is the statement behind simultaneous confidence rectangles for the coordinates of
`f(θ)`; the reference develops that construction as an illustration rather than as part of the
result, so it is not stated separately here. -/
theorem bootstrap_smooth_function_consistent [IsProbabilityMeasure P] [IsProbabilityMeasure Pr]
    -- LEAN-ONLY: the observations are measurable
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `P`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) P Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: the coordinate functions are measurable and square-integrable
    (hhmeas : ∀ j, Measurable (h j)) (hh2 : ∀ j, MemLp (h j) 2 P)
    -- USER-INPUT: `f` is differentiable at the parameter with nonzero continuous differential
    (hf : HasFDerivAt f Df (WithLp.toLp 2 fun j => ∫ s, h j s ∂P)) (hDf_ne : Df ≠ 0)
    -- USER-INPUT: the differential is continuous at the parameter
    (hf_cont : ContinuousAt (fderiv ℝ f) (WithLp.toLp 2 fun j => ∫ s, h j s ∂P))
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => supCDFDist
        (fun s => (Pr {ω' | nrm (f (meanStatistic h fun i : Fin n => X i ω') -
          f (WithLp.toLp 2 fun j => ∫ t, h j t ∂P)) ≤ s}).toReal)
        (fun s => ((bootstrapLaw fun i : Fin n => X i ω)
          {w | nrm (f (meanStatistic h w) -
            f (meanStatistic h fun i : Fin n => X i ω)) ≤ s}).toReal))
      atTop (𝓝 0) := by
  -- TODO (bootstrap delta method, uniform Pólya form). The sup-CDF (uniform) upgrade of
  -- `bootstrap_smooth_function_law_consistent`, obtained by feeding the smooth-function root into
  -- `tendsto_supCDFDist_bootstrap`: the norm of the delta-method limit `N(0, D covH Dᵀ)` has a
  -- continuous CDF (the `continuous_normLimitCDF` core, for the covariance `D covH Dᵀ`), turning
  -- pointwise CDF convergence into sup-distance convergence via the `PolyaUniformCDF` brick.
  -- Blocked on `smooth_function_of_means_tendsto` (delta-method Slutsky), the resampled-law
  -- bootstrap CLT, and the norm-CDF continuity core (`stdGaussian ≪ volume` + PosSemidef gaps).
  sorry

end SmoothFunctions

end StatLean.HypothesisTesting
