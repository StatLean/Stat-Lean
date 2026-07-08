import StatLean.Bayesian.Conjugacy.NormalNormal
import StatLean.Bayesian.ForMathlib.PiKernel

/-!
# The normal one-way hierarchy and partial pooling

The canonical hierarchical normal model `Y_j ∣ θ_j ∼ N(θ_j, σ²)`, `θ_j ∣ μ, τ² ∼ N(μ, τ²)`. Given
the hyperparameters, the group means have independent scalar Normal–Normal posteriors, whose mean
is a **convex combination** `(1−B)·y_j + B·μ` of the observation and the grand mean with shrinkage
weight `B = σ²/(σ²+τ²)` (partial pooling), and whose variance is strictly below the sampling
variance. Integrating out the group means, the data are i.i.d. `N(μ, σ²+τ²)`, so the
hyperparameter `μ` itself has a Normal–Normal posterior with `J` observations.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.2.5 (hierarchical extensions for the normal model), pp. 470–473;
§10.3 (optimality), p. 474.

**Proof formalization notes.** Every coupling reuses the Batch-2 `Conjugacy.NormalNormal` API: the
per-group posterior (`normal_normal_posterior_ae` at `n = 1`), the μ-posterior (the same at
`n = J`, noise variance `σ²+τ²`), and the marginal (`comp_gaussKernel_gaussianReal` per coordinate,
assembled with the diagonal product kernel `diagKernel`). The convex-combination mean and
`postVar < σ²` are scalar `postMean`/`postVar` real algebra (`field_simp`; `ht₀`, `hv` for the
nonzero denominators). No new posterior machinery is introduced.

**Bibliographic comments.** Partial pooling and shrinkage of group means toward a grand mean are
the content of C. Stein's estimator (1956) read hierarchically, and of the empirical-Bayes analysis
of D. V. Lindley and A. F. M. Smith (1972) and B. Efron and C. Morris ("Stein's estimation rule and
its competitors—an empirical Bayes approach," *J. Amer. Statist. Assoc.* 68 (1973), 117–130). The
one-way normal hierarchy is Robert's §10.2.5 running example.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The **shrinkage weight** `B = σ²/(σ²+τ²)` of the normal hierarchy (Robert §10.2.5). -/
noncomputable def shrinkageWeight (σ2 τ2 : ℝ≥0) : ℝ := (σ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))

/-- The shrinkage weight lies in `[0, 1]` (3C.3). -/
theorem shrinkageWeight_mem_Icc (σ2 τ2 : ℝ≥0) : shrinkageWeight σ2 τ2 ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- **Partial pooling** (3C.3): the per-group posterior mean is the convex combination
`(1−B)·y + B·μ` of the observation and the prior (grand) mean (Robert §10.2.5). -/
theorem normalHier_posteriorMean_convexCombination (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate prior and noise variances; Robert §10.2.5
    (hτ : τ2 ≠ 0) (hσ : σ2 ≠ 0) (y : ℝ) :
    postMean μ τ2 σ2 (fun _ : Fin 1 => y)
      = (1 - shrinkageWeight σ2 τ2) * y + shrinkageWeight σ2 τ2 * μ := by
  sorry

/-- **Variance reduction** (3C.4): the per-group posterior variance is strictly below the sampling
variance (Robert §10.2.5). -/
theorem normalHier_posteriorVar_lt_samplingVar (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate prior and noise variances; Robert §10.2.5
    (hτ : τ2 ≠ 0) (hσ : σ2 ≠ 0) :
    (postVar τ2 σ2 1 : ℝ) < (σ2 : ℝ) := by
  sorry

/-- **Marginal of the data given the hyperparameters** (3C.1): integrating out the group means, the
`J` groups are i.i.d. `N(μ, σ²+τ²)` (Robert §10.2.5). -/
theorem normalHier_marginal_y_given_hyper (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert §10.2.5
    (hσ : σ2 ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel; from `isMarkovKernel_gaussKernel hσ`
    [IsMarkovKernel (gaussKernel σ2)] (J : ℕ) :
    (diagKernel (gaussKernel σ2) J) ∘ₘ (Measure.pi fun _ : Fin J => gaussianReal μ τ2)
      = Measure.pi fun _ : Fin J => gaussianReal μ (τ2 + σ2) := by
  sorry

/-- **Posterior of the hyper-mean given `τ²`** (3C.5): with the group means integrated out, `μ` has
a Normal–Normal posterior from `J` i.i.d. observations of variance `σ²+τ²` (Robert §10.2.5). -/
theorem normalHier_muPosterior_given_tau (μ0 : ℝ) (t0 τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate hyperprior and marginal variances; Robert §10.2.5
    (ht0 : t0 ≠ 0) (hστ : σ2 + τ2 ≠ 0)
    -- LEAN-ONLY: Markov instance for the marginal Gaussian kernel
    [IsMarkovKernel (gaussKernel (σ2 + τ2))] (J : ℕ) :
    ∀ᵐ y ∂(iidKernel (gaussKernel (σ2 + τ2)) J ∘ₘ gaussianReal μ0 t0),
      ((iidKernel (gaussKernel (σ2 + τ2)) J) † gaussianReal μ0 t0) y
        = gaussianReal (postMean μ0 t0 (σ2 + τ2) y) (postVar t0 (σ2 + τ2) J) := by
  sorry

/-- **Per-group posterior given the hyperparameters** (3C.2, one coordinate): the group mean `θ_j`
has the scalar Normal–Normal posterior `N((1−B)y_j + B·μ, postVar)` (Robert §10.2.5). -/
theorem normalHier_thetaPosterior_given_mu_tau_coord (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate prior and noise variances; Robert §10.2.5
    (hτ : τ2 ≠ 0) (hσ : σ2 ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel
    [IsMarkovKernel (gaussKernel σ2)] :
    ∀ᵐ y ∂(iidKernel (gaussKernel σ2) 1 ∘ₘ gaussianReal μ τ2),
      ((iidKernel (gaussKernel σ2) 1) † gaussianReal μ τ2) y
        = gaussianReal (postMean μ τ2 σ2 y) (postVar τ2 σ2 1) := by
  sorry

end StatLean.Bayesian
