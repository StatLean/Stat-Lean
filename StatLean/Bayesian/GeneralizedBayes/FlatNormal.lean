import StatLean.Bayesian.GeneralizedBayes.Basic
import StatLean.Bayesian.Conjugacy.NormalNormal

/-!
# The flat-prior normal mean (canonical generalized-Bayes example)

For iid observations `xᵢ ~ 𝒩(μ, v)` and the improper flat prior `π(dμ) = dμ` (Lebesgue), the
generalized posterior is proper and Gaussian:
$$\mu \mid x_{1:n} \sim \mathcal N\big(\bar x,\ v/n\big).$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.5, Example 1.5.2 (`x ~ 𝒩(θ, 1)`, flat prior ⇒ posterior
`𝒩(x, 1)` — the `n = 1` case), p. 28; Example 1.5.1 (the flat prior as the location-invariant
choice), p. 27.

**Proof formalization notes.** The pointwise normalization engine applies with `π := volume`:
the product Gaussian likelihood completes the square in `μ` (the `sumSq_completion` lemma of
`Conjugacy.NormalNormal` with the prior term absent — equivalently its `t₀ → ∞` limit, proved
directly), exhibiting `volume.withDensity (∏ᵢ gaussianPDF μ v xᵢ)` as
`C(x) • gaussianReal x̄ (v/n)` with `C(x) ∈ (0, ∞)` for `n ≠ 0`. Note the abstract posterior
`κ†π` does not exist here (Lebesgue is not finite) — the statement is genuinely about
`generalizedPosterior`, which is the point of the example.

**Bibliographic comments.** The flat prior on a location parameter is Laplace's original
"principle of insufficient reason" (1774; Robert Example 1.5.1) and the simplest Jeffreys prior;
that it reproduces the frequentist answer `𝒩(x̄, v/n)` — with credible intervals numerically
equal to confidence intervals — is the classical reconciliation example. Robert §1.5 stresses both
its safety for estimation and (pp. 28–29) the Chapter-5 caveat that the arbitrary constant wrecks
Bayes factors, formalized in `GeneralizedBayes.Basic`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- **Flat-prior normal mean** (Robert Example 1.5.2, `n`-observation form): under the improper
Lebesgue prior, the generalized posterior from iid `𝒩(·, v)` data is `𝒩(x̄, v/n)`. -/
theorem flat_normal_generalizedPosterior {v : ℝ≥0}
    -- USER-INPUT: nondegenerate noise variance; Robert Example 1.5.2
    (hv : v ≠ 0) {n : ℕ}
    -- USER-INPUT: at least one observation (propriety needs it); Robert §1.5
    (hn : n ≠ 0) (x : Fin n → ℝ) :
    generalizedPosterior (fun (θ : ℝ) (x : Fin n → ℝ) => ∏ i, gaussianPDF θ v (x i))
        volume x
      = gaussianReal ((∑ i, x i) / n) (v / n) := sorry

end StatLean.Bayesian
