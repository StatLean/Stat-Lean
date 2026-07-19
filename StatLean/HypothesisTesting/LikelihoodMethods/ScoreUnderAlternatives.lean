import StatLean.HypothesisTesting.LikelihoodMethods.EstimatorUnderAlternatives

/-!
# The normalized score vector under local alternatives

Under quadratic-mean differentiability at `θ₀` the normalized score
`Zₙ = n^{-1/2} ∑_{i≤n} \tildeη_{θ₀}(Xᵢ)` is asymptotically `N(0, I(θ₀))` under `P^n_{θ₀}`.
Along a local alternative sequence `θₙ = θ₀ + hₙ/√n` with `hₙ → h` the limit is the *same
Gaussian shifted by* `I(θ₀)h`:
$$ Z_n \;\rightsquigarrow\; N\bigl(I(\theta_0)h,\; I(\theta_0)\bigr) \quad
   \text{under } P^n_{\theta_n}. $$
This is the exact statement that turns the score into a usable test statistic against local
alternatives: the alternative moves the mean of the limiting law by `I(θ₀)h` while leaving
the covariance unchanged, which is what makes the score test's local power computable.

**Reference.** Classical asymptotic likelihood theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The proof is the model application of Le Cam's third lemma. The area supplies every
  ingredient: `AsymptoticStatistics.AsymptoticRepresentation.contiguous_local_alternatives`
  for mutual contiguity of `P^n_{θ₀}` and `P^n_{θₙ}`;
  `AsymptoticStatistics.AsymptoticRepresentation.scoreSum_weakly_converges` and
  `joint_weak_conv_with_scoreSum` for the joint limit of `(Zₙ, log Lₙ,ₕ)` under `P^n_{θ₀}`;
  and then the third lemma itself, available in three shapes —
  `AsymptoticStatistics.Contiguity.weak_limit_under_Q_of_lecam_third` (exact log-ratio
  identity), `…_ennreal` (density form), and
  `…_of_integral_comparison` (asymptotic singular-mass control) — the last being the shape
  that avoids assuming a common support.
* The tilted limit produced by the third lemma is the Gaussian law with density
  proportional to `exp(⟪h, ·⟫)` against `N(0, I(θ₀))`, i.e. `N(I(θ₀)h, I(θ₀))`; the mean
  shift is the matrix action `mulVecE J h`.
* Statements use the same score `ℓ` that certifies quadratic-mean differentiability, which
  is the area's convention for `\tildeη_{θ₀} = 2η(·,θ₀)/√p_{θ₀}`; no separate definition of
  the score vector is introduced here.

**Bibliographic comments.** The score statistic is due to C. R. Rao ("Large sample tests of
statistical hypotheses concerning several parameters with applications to problems of
estimation," *Proc. Camb. Phil. Soc.* **44** (1948), 50–57). The contiguity machinery that
delivers its limit law under local alternatives is due to L. Le Cam ("Locally asymptotically
normal families of distributions," *Univ. California Publ. Statist.* **3** (1960), 37–98),
with the quadratic-mean differentiability hypothesis from L. Le Cam ("On the assumptions
used to prove asymptotic normality of maximum likelihood estimates," *Ann. Math. Statist.*
**41** (1970), 802–828).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- **The normalized score under local alternatives.**

If the model is differentiable in quadratic mean at `θ₀` with score `ℓ` and nonsingular
Fisher information matrix `J`, then along `θₙ = θ₀ + hₙ/√n` with `hₙ → h` the normalized
score sum satisfies `Zₙ ⇝ N(J·h, J)` under `P^n_{θₙ}`. -/
theorem weak_limit_scoreSum_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF` through
    -- `productMeasure_isProbabilityMeasure`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable; the model is a density family
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which quadratic-mean differentiability is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h)) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map (scoreSum ℓ n))
      (multivariateGaussian (mulVecE J h) J) := by
  sorry

end StatLean.HypothesisTesting
