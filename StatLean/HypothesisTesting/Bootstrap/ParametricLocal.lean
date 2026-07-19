import StatLean.HypothesisTesting.Bootstrap.Consistency
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The parametric bootstrap: plug-in at an estimated parameter, and local power

In a parametric model indexed by `θ` in a finite-dimensional parameter space, the bootstrap
substitutes an estimator `thHat n` for the unknown `θ` inside the sampling distribution
`Jpar n θ` of a root. Consistency here is a statement **in probability**, not almost surely:
the estimated parameter sequence does not stay inside any fixed local class with probability
one, only along suitably chosen subsequences.

This file contains:

* `tendsto_supCDFDist_parametric_fixed` — uniform convergence of the sampling distribution at
  the true parameter to the limit law;
* `tendstoInMeasure_supCDFDist_parametric_plugIn` — the plug-in display: the sampling
  distribution at the estimated parameter is uniformly close, in probability, to the one at the
  true parameter;
* `tendstoInMeasure_supCDFDist_parametric_bootstrap` — the two displays combined;
* `tendsto_bootstrapTest_local_power` — the limiting power of the bootstrap test against
  contiguous alternatives `θ + n^{-1/2} hdir`.

**Reference.** Classical parametric-bootstrap theory; original sources in the bibliographic
comments below.

**Designed deviation (subsequence route replaces the almost sure representation).** The
reference argument passes to an almost sure representation: it constructs, on a new probability
space, a copy of the estimator that converges almost surely, concludes the almost sure version
of the display for the copy, and transfers the conclusion back because the two estimators have
the same law. Constructing that representation is a substantial piece of machinery. We instead
take the **local uniformity over compact sets of local parameters** as the explicit hypothesis
(`hlocunif` below: convergence of the sampling distribution is uniform over parameters
`θ + n^{-1/2} t` with `‖t‖ ≤ M`) and drive the conclusion by the subsequence characterisation of
convergence in probability. The two routes prove the same display; the hypothesis we assume is
exactly the local uniformity that the reference derives from its local asymptotic theory.

**Designed deviation (tightness rather than bare consistency).** Mere consistency
`thHat n → θ` in probability does **not** activate a compact-`t` local uniformity hypothesis:
the estimator may leave every `n^{-1/2}`-neighbourhood of `θ`. The reference setup supplies
`n^{1/2}`-consistency through the efficiency of the estimator it uses. We therefore state the
honest input — uniform tightness of `n^{1/2}(thHat n − θ)` — which implies consistency and is
what the argument consumes.

**Proof formalization notes.**
* Convergence in probability of the uniform distance is `TendstoInMeasure` against the constant
  function `0`; the underlying distance on `ℝ` is the usual one.
* The local-uniformity hypothesis is stated in eventually-`∀`-`ε` form rather than as a
  supremum over a compact set, which avoids the junk value of a supremum over an index type
  that is not known to be nonempty.
* In `tendsto_bootstrapTest_local_power` the two hypotheses `hlocalCLT` and `hcritval` are
  **not** free-choice inputs: they are the local limit theory of the estimator under contiguous
  alternatives, and the convergence of the estimated critical value under those alternatives.
  They are recorded here as explicit hypotheses only because the local-asymptotics layer of
  this area is developed in a separate module; when that layer lands they must be discharged
  from it rather than supplied by callers. They are flagged as such on their tags.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). The class-of-sequences formulation of
consistency and the systematic study of bootstrap tests and their local power follow R. Beran
("Bootstrap methods in statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30)
and D. N. Politis, J. P. Romano and M. Wolf, *Subsampling*, Springer, 1999. Higher-order
properties of the parametric bootstrap are treated in P. Hall, *The Bootstrap and Edgeworth
Expansion*, Springer, 1992.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

section ParametricBootstrap

variable {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {Jpar : ℕ → EuclideanSpace ℝ (Fin k) → ℝ → ℝ} {Jlim : EuclideanSpace ℝ (Fin k) → ℝ → ℝ}
  {θ : EuclideanSpace ℝ (Fin k)} {thHat : ℕ → Ω → EuclideanSpace ℝ (Fin k)}

/-- **Sampling distribution at the true parameter converges uniformly to the limit law.**

Pointwise convergence of the sampling distribution functions at the fixed parameter `θ`,
together with continuity of the limit law, gives uniform convergence. -/
theorem tendsto_supCDFDist_parametric_fixed
    -- USER-INPUT: each sampling distribution is a distribution function
    (hcdf : ∀ n : ℕ, IsCDF (Jpar n θ))
    -- USER-INPUT: the limit law is a distribution function
    (hlim_cdf : IsCDF (Jlim θ))
    -- USER-INPUT: the limit law is continuous; the exact continuity requirement behind the
    -- upgrade from pointwise to uniform convergence
    (hlim_cont : Continuous (Jlim θ))
    -- USER-INPUT: pointwise convergence of the sampling distribution functions at `θ`
    (hptwise : ∀ x : ℝ, Tendsto (fun n => Jpar n θ x) atTop (𝓝 (Jlim θ x))) :
    Tendsto (fun n => supCDFDist (Jpar n θ) (Jlim θ)) atTop (𝓝 0) := by
  sorry

/-- **Plug-in display for the parametric bootstrap.**

If the sampling distribution converges to the limit law uniformly over parameters in
`n^{-1/2}`-neighbourhoods of `θ` of bounded rescaled radius, and if `n^{1/2}(thHat n − θ)` is
uniformly tight, then substituting the estimator for the true parameter perturbs the sampling
distribution by a uniformly negligible amount, in probability. -/
theorem tendstoInMeasure_supCDFDist_parametric_plugIn
    -- USER-INPUT: local uniformity over compact sets of local parameters — convergence of the
    -- sampling distribution to the limit law, uniform over `θ + n^{-1/2} t` with `‖t‖ ≤ M`
    (hlocunif : ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ M →
        supCDFDist (Jpar n (θ + (Real.sqrt n)⁻¹ • t)) (Jlim θ) ≤ ε)
    -- USER-INPUT: uniform tightness of the rescaled estimation error; strictly stronger than
    -- consistency and exactly what the local uniformity above consumes
    (htight : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ n : ℕ, (ℙ {ω | M < ‖Real.sqrt n • (thHat n ω - θ)‖}).toReal ≤ ε)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hcdf : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin k)), IsCDF (Jpar n t))
    -- USER-INPUT: the limit law is continuous
    (hlim_cont : Continuous (Jlim θ))
    -- LEAN-ONLY: the estimator is measurable; needed for the tightness sets and the conclusion
    -- to carry their measures
    (hmeas : ∀ n, Measurable (thHat n)) :
    TendstoInMeasure ℙ (fun n ω => supCDFDist (Jpar n (thHat n ω)) (Jpar n θ)) atTop
      (fun _ => 0) := by
  sorry

/-- **Parametric bootstrap consistency**, the two displays combined: the sampling distribution
at the estimated parameter is uniformly close, in probability, to the limit law. -/
theorem tendstoInMeasure_supCDFDist_parametric_bootstrap
    -- USER-INPUT: local uniformity over compact sets of local parameters
    (hlocunif : ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ M →
        supCDFDist (Jpar n (θ + (Real.sqrt n)⁻¹ • t)) (Jlim θ) ≤ ε)
    -- USER-INPUT: uniform tightness of the rescaled estimation error
    (htight : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ n : ℕ, (ℙ {ω | M < ‖Real.sqrt n • (thHat n ω - θ)‖}).toReal ≤ ε)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hcdf : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin k)), IsCDF (Jpar n t))
    -- USER-INPUT: the limit law is a distribution function and is continuous
    (hlim_cdf : IsCDF (Jlim θ)) (hlim_cont : Continuous (Jlim θ))
    -- LEAN-ONLY: measurability of the estimator
    (hmeas : ∀ n, Measurable (thHat n)) :
    TendstoInMeasure ℙ (fun n ω => supCDFDist (Jpar n (thHat n ω)) (Jlim θ)) atTop
      (fun _ => 0) := by
  sorry

/-- **Limiting local power of the bootstrap test.**

Test `g(θ) = 0` against `g(θ) > 0` by rejecting when `n^{1/2} g(thHat n)` exceeds the estimated
`1 − α` quantile. Against the contiguous alternatives `θ + n^{-1/2} hdir` the rejection
probability converges to `1 − Φ(z_{1−α} − σ⁻¹ ⟪∇g(θ), hdir⟫)`, where `σ²` is the variance of
the limiting law of the root at `θ`. -/
theorem tendsto_bootstrapTest_local_power
    {Pn : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} {g : EuclideanSpace ℝ (Fin k) → ℝ}
    {gradg hdir : EuclideanSpace ℝ (Fin k)} {sigma α : ℝ}
    -- USER-INPUT: the laws of the data of each sample size and each parameter value
    (hPn : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure (Pn n t))
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: the tested parameter lies on the boundary of the null hypothesis
    (hg0 : g θ = 0)
    -- USER-INPUT: `g` is differentiable at `θ` with gradient `gradg`
    (hgrad : HasGradientAt g gradg θ)
    -- USER-INPUT: the gradient does not vanish, so the limiting law of the root is nondegenerate
    (hgrad_ne : gradg ≠ 0)
    -- USER-INPUT: positive limiting standard deviation of the root at `θ`
    (hsigma : 0 < sigma)
    -- USER-INPUT: the limit law of the root at `θ` is centred normal with variance `sigma ^ 2`
    (hJlim_eq : ∀ x : ℝ, Jlim θ x = normalCDF 0 (Real.toNNReal (sigma ^ 2)) x)
    -- USER-INPUT: under the contiguous alternatives the rescaled test statistic is
    -- asymptotically normal, centred at the directional derivative. NOT a free choice —
    -- supplied by the local-asymptotics layer; see the file's proof formalization notes
    (hlocalCLT : ∀ x : ℝ, Tendsto (fun n : ℕ =>
        ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | Real.sqrt n * g (thHat n ω) - ⟪gradg, hdir⟫ ≤ x}).toReal) atTop
        (𝓝 (normalCDF 0 (Real.toNNReal (sigma ^ 2)) x)))
    -- USER-INPUT: under the contiguous alternatives the estimated critical value converges in
    -- probability to the critical value of the limit law. NOT a free choice — supplied by the
    -- plug-in theorem above with contiguity; see the file's proof formalization notes
    (hcritval : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
        ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | ε ≤ |cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α)
                - sigma * stdNormalQuantile (1 - α)|}).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        ((Pn n (θ + (Real.sqrt n)⁻¹ • hdir))
          {ω | cdfPseudoInverse (Jpar n (thHat n ω)) (1 - α) < Real.sqrt n * g (thHat n ω)}).toReal)
      atTop
      (𝓝 (1 - stdNormalCDF (stdNormalQuantile (1 - α) - sigma⁻¹ * ⟪gradg, hdir⟫))) := by
  sorry

end ParametricBootstrap

end StatLean.HypothesisTesting
