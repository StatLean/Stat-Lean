import StatLean.Bayesian.Conjugacy.Defs
import StatLean.Bayesian.Conjugacy.Criterion
import StatLean.Bayesian.ForMathlib.IIDKernel
import StatLean.Bayesian.Updating.Defs

/-!
# Normal-Normal conjugacy (known variance) and the normal posterior predictive

For a mean `μ ~ 𝒩(m₀, t₀)` and iid observations `xᵢ ~ 𝒩(μ, v)` with known noise variance `v`:

* **posterior** (Robert Table 3.3.1 / §4.4.1): `μ | x_{1:n} ~ 𝒩(postMean, postVar)` with
  `postVar = (t₀⁻¹ + n v⁻¹)⁻¹` and `postMean = postVar · (m₀/t₀ + (∑xᵢ)/v)`;
* **posterior predictive**: a future observation satisfies
  `x_{n+1} | x_{1:n} ~ 𝒩(postMean, postVar + v)` — posterior uncertainty plus noise.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Table 3.3.1 (Normal row: 𝒩(θ,σ²) + 𝒩(μ,τ²) →
𝒩(ϱ(σ²μ+τ²x), ϱσ²τ²), ϱ⁻¹ = σ²+τ²), p. 121; §4.4.1 (multivariate known-Σ update), p. 186;
Table 4.2.1, p. 176. The predictive has no numbered statement in Robert (general form is
eq. (4.1.5), p. 172) — flagged per our citation audit.

**Proof formalization notes.** The heart is a real **sum-of-squares (completing the square)
identity**: `(θ−m₀)²/t₀ + ∑ᵢ(xᵢ−θ)²/v = (θ−postMean)²/postVar + R(x)` with `R` independent of
`θ` (`field_simp` + `ring` with the nonzeroness of `t₀`, `v`, and `postVar`); exponentiating gives
the pointwise recognized form for the criterion (`gaussianReal_of_var_ne_zero` on both sides).
The predictive composes the posterior with one more Gaussian: `gaussKernel v ∘ₘ gaussianReal m V =
gaussianReal m (V + v)` — the bind-is-convolution step, closed by the pinned
`gaussianReal_conv_gaussianReal`. The Gaussian kernel is Markov only for `v ≠ 0` (at `v = 0` the
`withDensity` construction degenerates to the zero kernel), so statements carry the instance
`[IsMarkovKernel (gaussKernel v)]`, discharged by `isMarkovKernel_gaussKernel hv` — a LEAN-ONLY
plumbing argument, not a statistical assumption beyond `v ≠ 0`.

**Bibliographic comments.** The Gaussian-mean update with Gaussian prior is Gauss's own
combination-of-observations calculus (*Theoria motus*, 1809) read as Bayesian shrinkage; the
precision-weighted form is the basis of the Kalman filter (R. E. Kalman, *J. Basic Eng.* 82
(1960), 35–45 — sequential Normal-Normal updating) and of credibility formulas in actuarial
science. Robert presents it as the canonical conjugate pair (Tables 3.3.1/4.2.1, §4.4).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The Gaussian known-variance kernel is Markov for nonzero variance. -/
theorem isMarkovKernel_gaussKernel {v : ℝ≥0}
    -- USER-INPUT: nondegenerate noise variance; Robert Table 3.3.1
    (hv : v ≠ 0) :
    IsMarkovKernel (gaussKernel v) := sorry

/-- **Sum-of-squares (completing the square)**: the prior-plus-likelihood exponent is the
posterior exponent plus a `θ`-free remainder. -/
theorem sumSq_completion {m₀ : ℝ} {t₀ v : ℝ≥0}
    -- USER-INPUT: nondegenerate prior and noise variances; Robert Table 3.3.1
    (ht₀ : t₀ ≠ 0) (hv : v ≠ 0) {n : ℕ} (x : Fin n → ℝ) (θ : ℝ) :
    (θ - m₀) ^ 2 / (t₀ : ℝ) + ∑ i, (x i - θ) ^ 2 / (v : ℝ)
      = (θ - postMean m₀ t₀ v x) ^ 2 / (postVar t₀ v n : ℝ)
        + ((∑ i, (x i) ^ 2) / (v : ℝ) + m₀ ^ 2 / (t₀ : ℝ)
            - postMean m₀ t₀ v x ^ 2 / (postVar t₀ v n : ℝ)) := sorry

/-- **Normal-Normal posterior, known variance** (Robert Table 3.3.1 / §4.4.1): iid Gaussian
observations update `𝒩(m₀, t₀)` to `𝒩(postMean, postVar)`, predictive-a.e. -/
theorem normal_normal_posterior_ae {m₀ : ℝ} {t₀ v : ℝ≥0}
    -- USER-INPUT: nondegenerate prior and noise variances; Robert Table 3.3.1
    (ht₀ : t₀ ≠ 0) (hv : v ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel; from `isMarkovKernel_gaussKernel hv`
    [IsMarkovKernel (gaussKernel v)] (n : ℕ) :
    ∀ᵐ x ∂(iidKernel (gaussKernel v) n ∘ₘ gaussianReal m₀ t₀),
      ((iidKernel (gaussKernel v) n)†(gaussianReal m₀ t₀)) x
        = gaussianReal (postMean m₀ t₀ v x) (postVar t₀ v n) := sorry

/-- **Bind is convolution for Gaussians**: pushing a Gaussian law through the Gaussian kernel adds
the variances. -/
theorem comp_gaussKernel_gaussianReal {v : ℝ≥0}
    -- USER-INPUT: nondegenerate noise variance; Robert Table 3.3.1
    (hv : v ≠ 0) (m : ℝ) (V : ℝ≥0) :
    gaussKernel v ∘ₘ gaussianReal m V = gaussianReal m (V + v) := sorry

/-- **Normal posterior predictive** (Robert eq. (4.1.5) specialized): a future observation is
Gaussian with the posterior mean and variance `postVar + v`, predictive-a.e. -/
theorem normal_normal_posteriorPredictive_ae {m₀ : ℝ} {t₀ v : ℝ≥0}
    -- USER-INPUT: nondegenerate prior and noise variances; Robert Table 3.3.1
    (ht₀ : t₀ ≠ 0) (hv : v ≠ 0)
    -- LEAN-ONLY: Markov instance for the Gaussian kernel; from `isMarkovKernel_gaussKernel hv`
    [IsMarkovKernel (gaussKernel v)] (n : ℕ) :
    ∀ᵐ x ∂(iidKernel (gaussKernel v) n ∘ₘ gaussianReal m₀ t₀),
      posteriorPredictive (iidKernel (gaussKernel v) n) (gaussKernel v) (gaussianReal m₀ t₀) x
        = gaussianReal (postMean m₀ t₀ v x) (postVar t₀ v n + v) := sorry

end StatLean.Bayesian
