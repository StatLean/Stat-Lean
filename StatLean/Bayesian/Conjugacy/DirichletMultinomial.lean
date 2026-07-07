import StatLean.Bayesian.ForMathlib.DirichletDist
import StatLean.Bayesian.ForMathlib.MultinomialDist
import StatLean.Bayesian.Conjugacy.Criterion

/-!
# Dirichlet-Multinomial conjugacy

For category probabilities with a Dirichlet prior (corner parametrization, `k + 1` categories)
and one multinomial observation of `n` trials:
$$\theta \sim \mathcal D_{k+1}(\alpha), \quad v \mid \theta \sim \mathcal M_{k+1}(n;
\mathrm{simplexExtend}\ \theta) \ \Longrightarrow\
\theta \mid v \sim \mathcal D_{k+1}(\alpha + v) \qquad \text{predictive-a.e.}$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Table 3.3.1 (Multinomial ℳ_k(θ) + Dirichlet 𝒟(α) →
𝒟(α₁+x₁, …, α_k+x_k)), p. 121; Appendix A.8/A.11, p. 521; Example 3.3.4 (Dirichlet as an
exponential family), p. 116.

**Proof formalization notes.** The conjugacy kernel `dmKernel` is the multinomial kernel pulled
back along `simplexExtend`, so it is dominated by counting measure on the countable data space
`Fin (k+1) → ℕ` — the Batch-1 dominated machinery applies verbatim. Pointwise algebra on the open
corner: `dirichletWeight α θ · q(v | simplexExtend θ) = multinomial coefficient ·
dirichletWeight (α + v) θ` (`Real.rpow_natCast`, `rpow_add` on positive coordinates,
`Fin.snoc_castSucc`/`snoc_last`, `Fin.prod_univ_castSucc`); off the corner both sides vanish. The
recognized constant is `(dirichletZ α)⁻¹ · multinomial · dirichletZ (α + v)`, nondegenerate by
`dirichletZ_pos`/`dirichletZ_lt_top`, and the criterion closes the identification.

**Bibliographic comments.** Dirichlet-multinomial updating — "add the counts to the
concentrations" — is the categorical analogue of Laplace smoothing and the conjugate core of
finite mixture models, latent Dirichlet allocation (D. M. Blei, A. Y. Ng, M. I. Jordan, "Latent
Dirichlet allocation," *J. Mach. Learn. Res.* 3 (2003), 993–1022), and, in the infinite limit, the
Dirichlet-process machinery of Bayesian nonparametrics (T. S. Ferguson, *Ann. Statist.* 1 (1973),
209–230; Robert §1.8.2). Robert lists the pair among the natural conjugate families of
Raiffa–Schlaifer (Table 3.3.1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {k : ℕ}

/-- The **Dirichlet-Multinomial conjugacy kernel**: the multinomial experiment on the full
probability vector, pulled back to the corner parametrization. -/
@[reducible]
noncomputable def dmKernel (k n : ℕ) : Kernel (Fin k → ℝ) (Fin (k + 1) → ℕ) :=
  (multinomialKernel (k + 1) n).comap simplexExtend measurable_simplexExtend

/-- Pointwise weight algebra on the corner: Dirichlet weight times multinomial likelihood is the
multinomial coefficient times the updated Dirichlet weight. Off the corner both sides vanish. -/
theorem dirichletWeight_mul_multinomialWeight {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Robert Appendix A.8
    (hα : ∀ i, 0 < α i) (n : ℕ) (v : Fin (k + 1) → ℕ)
    -- USER-INPUT: the observed counts total `n` trials; Robert Appendix A.11
    (hv : ∑ i, v i = n) (θ : Fin k → ℝ) :
    dirichletWeight α θ * multinomialWeight (k + 1) n (simplexExtend θ) v
      = ENNReal.ofReal (Nat.multinomial Finset.univ v : ℝ)
          * dirichletWeight (α + fun i => (v i : ℝ)) θ := sorry

/-- **Dirichlet-Multinomial posterior** (Robert Table 3.3.1): observing counts `v` updates
`𝒟(α)` to `𝒟(α + v)`, predictive-a.e. -/
theorem dirichlet_multinomial_posterior_ae {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Robert Appendix A.8
    (hα : ∀ i, 0 < α i)
    -- LEAN-ONLY: instance plumbing, derivable from hα via `isProbabilityMeasure_dirichletMeasure`
    [IsFiniteMeasure (dirichletMeasure α)] (n : ℕ) :
    ∀ᵐ v ∂(dmKernel k n ∘ₘ dirichletMeasure α),
      ((dmKernel k n)†(dirichletMeasure α)) v
        = dirichletMeasure (α + fun i => (v i : ℝ)) := sorry

end StatLean.Bayesian
