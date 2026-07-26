import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

/-! ## Analytic infrastructure for the norm of a Gaussian vector

The limiting distribution function of a norm of the Gaussian limit is continuous because the
spheres of the norm are null for the limit law. The chain of facts below establishes that,
degeneracy of the covariance included: the Gaussian is the image of the standard Gaussian under
the square root of the covariance, that image turns the norm into a **seminorm** `g`, the level
sets of a nonzero seminorm are frontiers of convex sets and hence Lebesgue-null, and the standard
Gaussian is absolutely continuous with respect to the volume. -/

section NormOfGaussian

/-- Absolute continuity is inherited by finite powers of a measure on the line. Mathlib
v4.29.1 has `Measure.AbsolutelyContinuous.prod` for binary products but no `Measure.pi`
counterpart; this is the induction that turns one into the other. -/
private lemma pi_absolutelyContinuous_pi {μ ν : Measure ℝ} [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≪ ν) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ) ≪ (Measure.pi fun _ : Fin n => ν) := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
  | succ n ih =>
      have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).symm
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      rw [← hμ.map_eq, ← hν.map_eq]
      exact (h.prod ih).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable

/-- The standard Gaussian measure on a Euclidean space is absolutely continuous with respect to
the volume: it is the image under `WithLp.toLp` of a product of one-dimensional Gaussians, and
`WithLp.toLp` also transports the volume to the volume. -/
private lemma stdGaussian_absolutelyContinuous_volume (k : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))) ≪ (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
  have h1 : (stdGaussian (EuclideanSpace ℝ (Fin k)))
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (WithLp.toLp 2) :=
    map_pi_eq_stdGaussian.symm
  have h2 : (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = (Measure.pi fun _ : Fin k => (volume : Measure ℝ)).map (WithLp.toLp 2) := by
    rw [← volume_pi]
    exact (PiLp.volume_preserving_toLp (Fin k)).map_eq.symm
  rw [h1, h2]
  exact (pi_absolutelyContinuous_pi (gaussianReal_absolutelyContinuous 0 one_ne_zero) k).map
    (PiLp.volume_preserving_toLp (Fin k)).measurable

section Seminorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An absolutely homogeneous functional vanishes at the origin. -/
private lemma seminorm_zero {g : E → ℝ} (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) :
    g 0 = 0 := by simpa using hsmul 0 0

/-- A subadditive absolutely homogeneous functional is nonnegative. -/
private lemma seminorm_nonneg {g : E → ℝ} (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) (y : E) : 0 ≤ g y := by
  have h0 : g 0 = 0 := seminorm_zero hsmul
  have hneg : g ((-1 : ℝ) • y) = g y := by rw [hsmul]; simp
  have hy : y + (-1 : ℝ) • y = 0 := by module
  have h := hadd y ((-1 : ℝ) • y)
  rw [hneg, hy, h0] at h
  linarith

/-- A subadditive absolutely homogeneous functional is even. -/
private lemma seminorm_neg {g : E → ℝ} (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) (y : E) :
    g (-y) = g y := by
  have h := hsmul (-1) y
  simpa using h

/-- A subadditive absolutely homogeneous functional is convex. -/
private lemma convexOn_of_seminorm {g : E → ℝ} (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) : ConvexOn ℝ Set.univ g := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc g (a • x + b • y) ≤ g (a • x) + g (b • y) := hadd _ _
    _ = a * g x + b * g y := by rw [hsmul, hsmul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- A subadditive absolutely homogeneous functional on a finite-dimensional space is continuous:
it is convex and finite everywhere, hence locally Lipschitz. -/
private lemma continuous_of_seminorm [FiniteDimensional ℝ E] {g : E → ℝ}
    (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : E), g (c • y) = |c| * g y) : Continuous g :=
  (convexOn_of_seminorm hadd hsmul).locallyLipschitz.continuous

end Seminorm

/-- **The level sets of a nonvanishing seminorm are Lebesgue-null.**

For `x < 0` the level set is empty. For `x ≥ 0` it is contained in the frontier of the convex
sublevel set `{g ≤ x}`, which is Haar-null. The two ingredients that keep the point `y` off the
interior are: for `x > 0`, that `(1 + t) • y` leaves the sublevel set; and for `x = 0`, that a
proper subspace has empty interior. -/
private lemma volume_seminorm_level_eq_zero {k : ℕ} {g : EuclideanSpace ℝ (Fin k) → ℝ}
    (hadd : ∀ y z, g (y + z) ≤ g y + g z)
    (hsmul : ∀ (c : ℝ) (y : EuclideanSpace ℝ (Fin k)), g (c • y) = |c| * g y)
    (hne : ∃ u, g u ≠ 0) (x : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) {y | g y = x} = 0 := by
  have hnn := seminorm_nonneg hadd hsmul
  have h0 : g 0 = 0 := seminorm_zero hsmul
  obtain ⟨u, hu⟩ := hne
  have hupos : 0 < g u := lt_of_le_of_ne (hnn u) (Ne.symm hu)
  have hune : u ≠ 0 := fun h => by rw [h, h0] at hupos; exact lt_irrefl _ hupos
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hune
  rcases lt_or_ge x 0 with hx | hx
  · have hempty : {y : EuclideanSpace ℝ (Fin k) | g y = x} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ hnn y) (not_le.mpr hx)
    rw [hempty, measure_empty]
  · have hconv : Convex ℝ {y : EuclideanSpace ℝ (Fin k) | g y ≤ x} := by
      have h := (convexOn_of_seminorm hadd hsmul).convex_le x
      simpa using h
    refine measure_mono_null ?_ (Convex.addHaar_frontier _ hconv)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    refine ⟨subset_closure (by simp only [Set.mem_setOf_eq, hy]; exact le_rfl), ?_⟩
    intro hmem
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hmem)
    have hune' : ‖u‖ ≠ 0 := hunorm.ne'
    rcases eq_or_lt_of_le hx with hx0 | hxpos
    · -- the level `x = 0` is the kernel of `g`, a proper subspace, so it has empty interior
      obtain ⟨s, hs, hnormsu⟩ : ∃ s : ℝ, 0 < s ∧ s * ‖u‖ = ε / 2 :=
        ⟨ε / (2 * ‖u‖), by positivity, by field_simp⟩
      have hzmem : y + s • u ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs, hnormsu]
        linarith
      have hz : g (y + s • u) ≤ x := hball hzmem
      have hsplit : g (s • u) ≤ g (y + s • u) + g (-y) := by
        have := hadd (y + s • u) (-y)
        simpa using this
      rw [seminorm_neg hsmul, hsmul, abs_of_pos hs, hy, ← hx0] at hsplit
      nlinarith [hsplit, hz, hupos, hs]
    · -- a positive level: scaling `y` slightly leaves the sublevel set
      have hyne : y ≠ 0 := fun h => by rw [h, h0] at hy; exact hxpos.ne hy
      have hynorm : 0 < ‖y‖ := norm_pos_iff.2 hyne
      have hyne' : ‖y‖ ≠ 0 := hynorm.ne'
      obtain ⟨t, ht, hnormty⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖y‖ = ε / 2 :=
        ⟨ε / (2 * ‖y‖), by positivity, by field_simp⟩
      have hzmem : (1 + t) • y ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hrw : (1 + t) • y - y = t • y := by module
        rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnormty]
        linarith
      have hz : g ((1 + t) • y) ≤ x := hball hzmem
      rw [hsmul, abs_of_pos (by linarith : (0 : ℝ) < 1 + t), hy] at hz
      nlinarith [hz, ht, hxpos]

open scoped MatrixOrder

/-- The coordinates of a square-integrable law on a Euclidean space are square-integrable. -/
private lemma memLp_coord {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q) (i : Fin k) :
    MemLp (fun y : EuclideanSpace ℝ (Fin k) => WithLp.ofLp y i) 2 Q := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin k) i).comp_memLp' hQ2
  simpa [Function.comp_def] using h

/-- The covariance bilinear form of a square-integrable law on a Euclidean space is the
quadratic form of its covariance matrix. -/
private lemma covarianceBilin_eq_covMatrix {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    [IsFiniteMeasure Q] (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    (x y : EuclideanSpace ℝ (Fin k)) :
    covarianceBilin Q x y = ∑ i, ∑ j, WithLp.ofLp x i * WithLp.ofLp y j * covMatrix Q i j := by
  have hmap : Q.map (fun y : EuclideanSpace ℝ (Fin k) =>
      WithLp.toLp 2 fun i => WithLp.ofLp y i) = Q := by
    simp
  have h := covarianceBilin_apply_pi (μ := Q)
    (X := fun (i : Fin k) (y : EuclideanSpace ℝ (Fin k)) => WithLp.ofLp y i) (memLp_coord hQ2) x y
  rwa [hmap] at h

/-- The variance of a linear functional is the quadratic form of the covariance matrix. -/
private lemma variance_inner_eq_covMatrix {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    [IsFiniteMeasure Q] (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    (t : EuclideanSpace ℝ (Fin k)) :
    Var[fun z : EuclideanSpace ℝ (Fin k) => inner ℝ t z; Q]
      = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix Q i j := by
  rw [← covarianceBilin_self hQ2 t, covarianceBilin_eq_covMatrix hQ2]

/-- **The covariance matrix of a square-integrable law is positive semidefinite.**

Square-integrability is what makes this true: the Mathlib `covariance` returns its junk value `0`
on entries whose integrand is not integrable, and a matrix built from a mixture of genuine and
junk entries need not be positive semidefinite. -/
private lemma posSemidef_covMatrix {k : ℕ} {Q : Measure (EuclideanSpace ℝ (Fin k))}
    [IsFiniteMeasure Q] (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q) :
    (covMatrix Q).PosSemidef := by
  classical
  have hbil := covarianceBilin_eq_covMatrix hQ2
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, covMatrix, Matrix.of_apply]
    exact covariance_comm _ _
  · intro x
    have h := covarianceBilin_self_nonneg (μ := Q) (WithLp.toLp 2 x)
    rw [hbil] at h
    have hrw : dotProduct (star x) ((covMatrix Q).mulVec x)
        = ∑ i, ∑ j, x i * x j * covMatrix Q i j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hrw]
    exact h

/-- **The spheres of a norm are null for a nondegenerate Gaussian limit.**

The analytic core: `multivariateGaussian 0 S` is the image of the standard Gaussian under the
square root of `S`, and that image turns `nrm` into a seminorm `g = nrm ∘ √S` which does not
vanish identically as soon as `S ≠ 0`. Degeneracy of `S` is allowed. -/
private lemma measure_multivariateGaussian_norm_level {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    {nrm : EuclideanSpace ℝ (Fin k) → ℝ}
    (hpsd : S.PosSemidef) (hSne : S ≠ 0)
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    (hnrm_def : ∀ y, nrm y = 0 → y = 0) (x : ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S {z | nrm z = x} = 0 := by
  classical
  set A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hAdef
  set g : EuclideanSpace ℝ (Fin k) → ℝ := fun y => nrm (A y) with hgdef
  have hgadd : ∀ y z, g (y + z) ≤ g y + g z := by
    intro y z; simp only [hgdef, map_add]; exact hnrm_add _ _
  have hgsmul : ∀ (c : ℝ) (y), g (c • y) = |c| * g y := by
    intro c y; simp only [hgdef, map_smul]; exact hnrm_smul _ _
  -- the square root of a nonzero positive semidefinite matrix is nonzero
  have hsqrt_ne : CFC.sqrt S ≠ 0 := fun h => hSne ((CFC.sqrt_eq_zero_iff S hpsd.nonneg).1 h)
  have hAne : A ≠ 0 := by
    intro h
    exact hsqrt_ne ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)).injective
      (a₁ := CFC.sqrt S) (a₂ := 0) (by simpa [hAdef, map_zero] using h))
  -- hence `g` is a seminorm that does not vanish identically
  have hgne : ∃ u, g u ≠ 0 := by
    obtain ⟨u, hu⟩ := DFunLike.ne_iff.1 hAne
    refine ⟨u, fun h => hu ?_⟩
    simpa using hnrm_def _ h
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  have hset : MeasurableSet {z : EuclideanSpace ℝ (Fin k) | nrm z = x} :=
    measurableSet_eq_fun hnrm_cont.measurable measurable_const
  have hpre : (fun y : EuclideanSpace ℝ (Fin k) => (0 : EuclideanSpace ℝ (Fin k)) + A y) ⁻¹'
      {z | nrm z = x} = {y | g y = x} := by
    ext y; simp [hgdef]
  rw [multivariateGaussian,
    Measure.map_apply (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin k) =>
      (0 : EuclideanSpace ℝ (Fin k)) + A y) hset, hpre]
  exact stdGaussian_absolutelyContinuous_volume k
    (volume_seminorm_level_eq_zero hgadd hgsmul hgne x)

/-- **Continuity of the limiting norm distribution function, for a general covariance.**

The general engine behind `continuous_normLimitCDF`: for any nonzero positive semidefinite `S`
the distribution function of `nrm` under `multivariateGaussian 0 S` is continuous. Degeneracy of
`S` is allowed — only `S ≠ 0` is used. -/
private lemma continuous_normLimitCDF_of_posSemidef {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    {nrm : EuclideanSpace ℝ (Fin k) → ℝ}
    (hpsd : S.PosSemidef) (hSne : S ≠ 0)
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    (hnrm_def : ∀ y, nrm y = 0 → y = 0) :
    Continuous (normLimitCDF S nrm) := by
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  set ρ := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map nrm with hρdef
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map hnrm_cont.measurable.aemeasurable
  haveI : NoAtoms ρ := by
    refine ⟨fun x => ?_⟩
    rw [hρdef, Measure.map_apply hnrm_cont.measurable (measurableSet_singleton x)]
    exact measure_multivariateGaussian_norm_level hpsd hSne hnrm_add hnrm_smul hnrm_def x
  have heq : normLimitCDF S nrm = fun x => (ρ (Set.Iic x)).toReal := by
    funext x
    rw [normLimitCDF, hρdef, Measure.map_apply hnrm_cont.measurable measurableSet_Iic]
    rfl
  rw [heq]
  exact continuous_toReal_measure_Iic ρ

end NormOfGaussian

/-! ## Empirical measures on a Euclidean space -/

section EmpiricalBasics

/-- Every strongly measurable function is integrable against an empirical measure. -/
private lemma integrable_empiricalMeasure {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : Fin n → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin k) → E) : Integrable f (empiricalMeasure x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [empiricalMeasure]
  · unfold empiricalMeasure
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne'))
    exact integrable_finset_sum_measure.2 (fun i _ => integrable_dirac (by simp))

/-- The integral against an empirical measure is the sample average. -/
private lemma integral_empiricalMeasure {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (x : Fin n → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin k) → E) :
    ∫ y, f y ∂(empiricalMeasure x) = (n : ℝ)⁻¹ • ∑ i, f (x i) := by
  unfold empiricalMeasure
  rw [integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The empirical measure of a nonempty sample is a probability measure. -/
private lemma isProbabilityMeasure_empiricalMeasure {n : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin k)) : IsProbabilityMeasure (empiricalMeasure x) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]

/-- The identity is square-integrable against an empirical measure. -/
private lemma memLp_id_empiricalMeasure {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin k)) :
    MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 (empiricalMeasure x) := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  exact integrable_empiricalMeasure x (fun y => ‖y‖ ^ 2)

/-- **Strong law of large numbers, in the form the empirical class needs.** -/
private lemma tendsto_sample_average {Pr : Measure Ω}
    [IsProbabilityMeasure Pr] {Q : Measure (EuclideanSpace ℝ (Fin k))}
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    (g : EuclideanSpace ℝ (Fin k) → E) (hg : Measurable g) (hint : Integrable g Q) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω)) atTop
      (𝓝 (∫ y, g y ∂Q)) := by
  have hintmap : Integrable g (Pr.map (X 0)) := by rw [hlaw.map_eq]; exact hint
  have hint' : Integrable (fun ω => g (X 0 ω)) Pr :=
    (integrable_map_measure hintmap.aestronglyMeasurable (hmeas 0).aemeasurable).1 hintmap
  have hmean : Pr[fun ω => g (X 0 ω)] = ∫ y, g y ∂Q :=
    hlaw.integral_comp hg.aestronglyMeasurable
  rw [← hmean]
  exact strong_law_ae (fun i ω => g (X i ω)) hint'
    (fun i j hij => (hindep.comp (fun _ => g) (fun _ => hg)).indepFun hij)
    (fun i => (hident i).comp hg)

end EmpiricalBasics

/-! ## Cramér–Wold: projecting the mean-vector root onto a direction -/

section CramerWold

/-- The image of the mean-vector root law under a linear functional is the univariate root law
of the image sequence. This is the Cramér–Wold reduction, at the level of the laws. -/
private lemma meanVecRootLaw_map_inner {k : ℕ} (F : Measure (EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure F] (hF2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 F)
    (t : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    (meanVecRootLaw F n).map (fun z => inner ℝ t z)
      = meanRootLaw (F.map (fun z => inner ℝ t z)) n := by
  classical
  have hcoe : (fun z : EuclideanSpace ℝ (Fin k) => inner ℝ t z) = ⇑(innerSL ℝ t) := rfl
  simp only [hcoe]
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := innerSL ℝ t with hL
  have hLc : Continuous L := L.continuous
  have hFint : Integrable (fun z : EuclideanSpace ℝ (Fin k) => z) F := hF2.integrable one_le_two
  have hint2 : ∫ s, s ∂(F.map L) = L (∫ z, z ∂F) := by
    rw [integral_map hLc.aemeasurable (by fun_prop), L.integral_comp_comm hFint]
  have hpi : Measure.pi (fun _ : Fin n => F.map L)
      = (Measure.pi fun _ : Fin n => F).map (fun y i => L (y i)) :=
    (Measure.pi_map_pi (fun _ => hLc.aemeasurable)).symm
  rw [meanVecRootLaw, meanRootLaw, hpi,
    Measure.map_map hLc.measurable (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y
  simp only [Function.comp_def, hint2, map_smul, map_sub, map_sum, smul_eq_mul]

end CramerWold

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
  classical
  -- Replace the unconstrained `n = 0` entry of the sequence by `Q`, so that every entry is a
  -- probability measure; the conclusion only sees the tail.
  set F' : ℕ → Measure (EuclideanSpace ℝ (Fin k)) := fun n => if n = 0 then Q else F n with hF'def
  have hF'eq : ∀ n : ℕ, 0 < n → F' n = F n := by
    intro n hn; simp only [hF'def, if_neg hn.ne']
  haveI hF'prob : ∀ n, IsProbabilityMeasure (F' n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hF'def, if_pos rfl] using ‹IsProbabilityMeasure Q›
    · rw [hF'eq n hn]; exact hF.1 n hn
  obtain ⟨-, hF2, hFweak, hFmean, hFcov⟩ := hF
  have hF'2 : ∀ n, MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 (F' n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa only [hF'def, if_pos rfl] using hQ2
    · rw [hF'eq n hn]; exact hF2 n
  have hF'weak : ∀ g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      Tendsto (fun n => ∫ y, g y ∂(F' n)) atTop (𝓝 (∫ y, g y ∂Q)) := by
    intro g
    refine (hFweak g).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  have hF'mean : ∀ i : Fin k, Tendsto (fun n => ∫ y, WithLp.ofLp y i ∂(F' n)) atTop
      (𝓝 (∫ y, WithLp.ofLp y i ∂Q)) := by
    intro i
    refine (hFmean i).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  have hF'cov : ∀ i j : Fin k,
      Tendsto (fun n => covMatrix (F' n) i j) atTop (𝓝 (covMatrix Q i j)) := by
    intro i j
    refine (hFcov i j).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hF'eq n hn]
  -- the root laws are probability measures
  haveI hpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => F' n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (F' n) := fun _ => hF'prob n
    infer_instance
  haveI hroot : ∀ n : ℕ, IsProbabilityMeasure (meanVecRootLaw (F' n) n) := by
    intro n
    haveI := hpi n
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  -- Cramér–Wold, direction by direction, through the characteristic functions
  set μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    fun n => ⟨meanVecRootLaw (F' n) n, hroot n⟩ with hμs
  set ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    ⟨multivariateGaussian 0 (covMatrix Q), inferInstance⟩ with hν
  have hconv : Tendsto μs atTop (𝓝 ν) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    -- the projected sequence
    have hLc : Continuous fun z : EuclideanSpace ℝ (Fin k) => (inner ℝ t z : ℝ) :=
      (innerSL ℝ t).continuous
    set G : ℕ → Measure ℝ := fun n => (F' n).map (fun z => inner ℝ t z) with hG
    set Q₁ : Measure ℝ := Q.map (fun z => inner ℝ t z) with hQ₁
    haveI hGprob : ∀ n, IsProbabilityMeasure (G n) := fun n =>
      Measure.isProbabilityMeasure_map hLc.aemeasurable
    haveI hQ₁prob : IsProbabilityMeasure Q₁ := Measure.isProbabilityMeasure_map hLc.aemeasurable
    haveI hGpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => G n) := by
      intro n
      haveI : ∀ _ : Fin n, IsProbabilityMeasure (G n) := fun _ => hGprob n
      infer_instance
    haveI hGroot : ∀ n : ℕ, IsProbabilityMeasure (meanRootLaw (G n) n) := by
      intro n
      haveI := hGpi n
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    -- square-integrability of the projections
    have hproj2 : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))),
        MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 μ →
          MemLp (fun s : ℝ => s) 2 (μ.map (fun z => inner ℝ t z)) := by
      intro μ hμ
      refine (memLp_map_measure_iff (by fun_prop) hLc.aemeasurable).2 ?_
      have h : MemLp (fun z : EuclideanSpace ℝ (Fin k) => (inner ℝ t z : ℝ)) 2 μ := by
        simpa [Function.comp_def] using (innerSL ℝ t).comp_memLp' hμ
      simpa [Function.comp_def] using h
    have hG2 : ∀ n, MemLp (fun s : ℝ => s) 2 (G n) := fun n => hproj2 _ (hF'2 n)
    have hQ₁2 : MemLp (fun s : ℝ => s) 2 Q₁ := hproj2 _ hQ2
    -- weak convergence of the projections
    have hGweak : ∀ g : ℝ →ᵇ ℝ,
        Tendsto (fun n => ∫ s, g s ∂(G n)) atTop (𝓝 (∫ s, g s ∂Q₁)) := by
      intro g
      have hcomp : ∀ μ : Measure (EuclideanSpace ℝ (Fin k)),
          ∫ s, g s ∂(μ.map (fun z => inner ℝ t z))
            = ∫ y, (g.compContinuous ⟨fun z => inner ℝ t z, hLc⟩) y ∂μ := by
        intro μ
        rw [integral_map hLc.aemeasurable g.continuous.aestronglyMeasurable]
        rfl
      simp only [hG, hQ₁, hcomp]
      exact hF'weak _
    -- the means of the projections
    have hprojmean : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure μ],
        MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 μ →
          ∫ s, s ∂(μ.map (fun z => inner ℝ t z))
            = ∑ i, WithLp.ofLp t i * ∫ y, WithLp.ofLp y i ∂μ := by
      intro μ _ hμ
      have hint : Integrable (fun z : EuclideanSpace ℝ (Fin k) => z) μ := hμ.integrable one_le_two
      have hcomm : ∫ z, (inner ℝ t z : ℝ) ∂μ = inner ℝ t (∫ z, z ∂μ) :=
        (innerSL ℝ t).integral_comp_comm hint
      have hcoordint : ∀ i : Fin k, ∫ y, WithLp.ofLp y i ∂μ = WithLp.ofLp (∫ z, z ∂μ) i :=
        fun i => (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin k) i).integral_comp_comm hint
      rw [integral_map hLc.aemeasurable (by fun_prop), hcomm]
      simp only [hcoordint]
      simp [PiLp.inner_apply, real_inner_eq_re_inner, mul_comm]
    have hGmean : Tendsto (fun n => ∫ s, s ∂(G n)) atTop (𝓝 (∫ s, s ∂Q₁)) := by
      simp only [hG, hQ₁, hprojmean _ (hF'2 _), hprojmean _ hQ2]
      exact tendsto_finset_sum _ fun i _ => (hF'mean i).const_mul _
    -- the variances of the projections
    have hprojvar : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure μ],
        MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 μ →
          Var[fun s : ℝ => s; μ.map (fun z => inner ℝ t z)]
            = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix μ i j := by
      intro μ _ hμ
      rw [variance_map (by fun_prop) hLc.aemeasurable]
      exact variance_inner_eq_covMatrix hμ t
    have hGvar : Tendsto (fun n => Var[fun s : ℝ => s; G n]) atTop
        (𝓝 Var[fun s : ℝ => s; Q₁]) := by
      simp only [hG, hQ₁, hprojvar _ (hF'2 _), hprojvar _ hQ2]
      exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
        (hF'cov i j).const_mul _
    -- the univariate triangular-array central limit theorem in this direction
    have huni := tendsto_meanRootLaw hG2 hQ₁2 hGweak hGmean hGvar
    set ρs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨meanRootLaw (G n) n, hGroot n⟩ with hρs
    set ρ : ProbabilityMeasure ℝ :=
      ⟨gaussianReal 0 (Real.toNNReal Var[fun s : ℝ => s; Q₁]), inferInstance⟩ with hρ
    have hprobconv : Tendsto ρs atTop (𝓝 ρ) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 huni
    have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hprobconv 1
    -- transport back to the characteristic function of the vector law
    have hproject : ∀ (μ : Measure (EuclideanSpace ℝ (Fin k))),
        charFun μ t = charFun (μ.map (fun z => inner ℝ t z)) 1 := by
      intro μ
      have h1 : ∀ a : ℝ, (inner ℝ a (1 : ℝ) : ℝ) = a := fun a => by
        simp [real_inner_eq_re_inner]
      rw [charFun_apply, charFun_apply, integral_map hLc.aemeasurable (by fun_prop)]
      simp only [h1]
      simp_rw [real_inner_comm t]
    have hcoeμ : ∀ n : ℕ, ((μs n : Measure (EuclideanSpace ℝ (Fin k))))
        = meanVecRootLaw (F' n) n := fun n => rfl
    have hcoeν : ((ν : Measure (EuclideanSpace ℝ (Fin k))))
        = multivariateGaussian 0 (covMatrix Q) := rfl
    have hcoeρs : ∀ n : ℕ, ((ρs n : Measure ℝ)) = meanRootLaw (G n) n := fun n => rfl
    have hcoeρ : ((ρ : Measure ℝ))
        = gaussianReal 0 (Real.toNNReal Var[fun s : ℝ => s; Q₁]) := rfl
    have hlhs : ∀ n : ℕ, charFun (meanVecRootLaw (F' n) n) t
        = charFun (meanRootLaw (G n) n) 1 := by
      intro n
      rw [hproject]
      congr 1
      exact meanVecRootLaw_map_inner (F' n) (hF'2 n) t n
    have hrhs : charFun (multivariateGaussian 0 (covMatrix Q)) t
        = charFun (gaussianReal 0 (Real.toNNReal Var[fun s : ℝ => s; Q₁])) 1 := by
      have hvarQ : Var[fun s : ℝ => s; Q₁]
          = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix Q i j := hprojvar _ hQ2
      have hquad : WithLp.ofLp t ⬝ᵥ (covMatrix Q).mulVec (WithLp.ofLp t)
          = ∑ i, ∑ j, WithLp.ofLp t i * WithLp.ofLp t j * covMatrix Q i j := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hqnn : 0 ≤ WithLp.ofLp t ⬝ᵥ (covMatrix Q).mulVec (WithLp.ofLp t) := by
        simpa using (posSemidef_covMatrix hQ2).dotProduct_mulVec_nonneg (WithLp.ofLp t)
      rw [charFun_multivariateGaussian (posSemidef_covMatrix hQ2), charFun_gaussianReal,
        hvarQ, ← hquad]
      simp [Real.coe_toNNReal _ (variance_nonneg _ _), max_eq_left hqnn]
    simp only [hcoeμ, hcoeν, hlhs, hrhs]
    simp only [hcoeρs, hcoeρ] at hcf
    exact hcf
  -- unpack the weak convergence and undo the `n = 0` patch
  have hgoal := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv f
  refine hgoal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hμs]
  simp only [hF'eq n hn]
  rfl

/-- **The limiting distribution function of the norm is continuous.**

If the limiting covariance matrix has a nonzero entry, the norm of the Gaussian limit has no
atoms: the spheres of a norm are boundaries of convex sets and hence null for the limit law.

**Signature amendment (square-integrability of the limit law).** The reference's statement is
*false* as frozen, and the added hypotheses `[IsFiniteMeasure Q]` and `hQ2` are exactly what
repairs it. In Mathlib v4.29.1, `multivariateGaussian 0 S = Measure.dirac 0` as soon as `S` is
not positive semidefinite (`ProbabilityTheory.multivariateGaussian_of_not_posSemidef`); for that
law `normLimitCDF S nrm` is the indicator of `{0 ≤ x}`, which jumps at `0`, so no norm makes it
continuous. And `covMatrix Q` is positive semidefinite only under square-integrability: the
Mathlib `covariance` returns its junk value `0` whenever the integrand is not integrable, so a
law with one non-integrable coordinate can have a vanishing diagonal entry next to a genuine
nonzero off-diagonal one (on `ℝ²`, the law of `(Z, Z / (1 + Z²))` for a Cauchy `Z` has junk
`(1,1)` entry `0` — `Z` is not integrable and `Z²` is not either — while the `(1,2)` entry
`∫ Z² / (1 + Z²)` is finite and positive, giving a negative determinant). Both added hypotheses
are already carried by the two siblings `norm_root_cdf_tendsto` and
`bootstrap_meanVec_consistent`, so no application is weakened. -/
theorem continuous_normLimitCDF [IsFiniteMeasure Q]
    -- USER-INPUT (signature amendment): the limit law is square-integrable, so its covariance
    -- matrix is positive semidefinite and the Gaussian limit is a genuine Gaussian
    (hQ2 : MemLp (fun y : EuclideanSpace ℝ (Fin k) => y) 2 Q)
    -- USER-INPUT: the norm is subadditive
    (hnrm_add : ∀ y z, nrm (y + z) ≤ nrm y + nrm z)
    -- USER-INPUT: the norm is absolutely homogeneous
    (hnrm_smul : ∀ (c : ℝ) (y), nrm (c • y) = |c| * nrm y)
    -- USER-INPUT: the norm is positive definite
    (hnrm_def : ∀ y, nrm y = 0 → y = 0)
    -- USER-INPUT: the limiting covariance is not identically zero, so the limit is nondegenerate
    (hS : ∃ i j : Fin k, covMatrix Q i j ≠ 0) :
    Continuous (normLimitCDF (covMatrix Q) nrm) := by
  obtain ⟨i, j, hij⟩ := hS
  exact continuous_normLimitCDF_of_posSemidef (posSemidef_covMatrix hQ2)
    (fun h => hij (by rw [h]; simp)) hnrm_add hnrm_smul hnrm_def

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
  classical
  obtain ⟨i₀, j₀, hij⟩ := hS
  have hSne : covMatrix Q ≠ 0 := fun h => hij (by rw [h]; simp)
  have hpsd := posSemidef_covMatrix hQ2
  have hnrm_cont : Continuous nrm := continuous_of_seminorm hnrm_add hnrm_smul
  -- all the laws in sight are probability measures (`n = 0` gives the Dirac at the empty tuple)
  haveI hpi : ∀ n : ℕ, IsProbabilityMeasure (Measure.pi fun _ : Fin n => F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [Measure.pi_of_empty]; infer_instance
    · haveI := hF.1 n hn
      haveI : ∀ _ : Fin n, IsProbabilityMeasure (F n) := fun _ => ‹_›
      infer_instance
  haveI hroot : ∀ n : ℕ, IsProbabilityMeasure (meanVecRootLaw (F n) n) := by
    intro n
    haveI := hpi n
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  -- weak convergence of the root laws, packaged as `ProbabilityMeasure` convergence
  set ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    ⟨multivariateGaussian 0 (covMatrix Q), inferInstance⟩ with hν
  set μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    fun n => ⟨meanVecRootLaw (F n) n, hroot n⟩ with hμs
  have hconv : Tendsto μs atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f =>
      meanVec_root_tendsto hQ2 hF f
  -- the frontier of the sublevel set is contained in the sphere, which is Gaussian-null
  have hfrontier :
      (ν : Measure (EuclideanSpace ℝ (Fin k)))
        (frontier {z : EuclideanSpace ℝ (Fin k) | nrm z ≤ x}) = 0 := by
    refine measure_mono_null ?_
      (measure_multivariateGaussian_norm_level hpsd hSne hnrm_add hnrm_smul hnrm_def x)
    intro z hz
    have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin k) | nrm z ≤ x} :=
      isClosed_le hnrm_cont continuous_const
    have hz1 : nrm z ≤ x := by
      have h := hz.1
      rwa [hclosed.closure_eq] at h
    exact le_antisymm hz1 (not_lt.1 fun hlt => hz.2
      (mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset ((isOpen_lt hnrm_cont continuous_const).mem_nhds hlt)
          (fun w hw => (le_of_lt hw : nrm w ≤ x)))))
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hfrontier
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport

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
