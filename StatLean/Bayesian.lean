import StatLean.Bayesian.ForMathlib.PiWithDensity
import StatLean.Bayesian.ForMathlib.IIDKernel
import StatLean.Bayesian.ForMathlib.KernelMixture
import StatLean.Bayesian.ForMathlib.MultinomialDist
import StatLean.Bayesian.ForMathlib.DirichletDist
import StatLean.Bayesian.ForMathlib.PiKernel
import StatLean.Bayesian.ForMathlib.GaussianDeriv
import StatLean.Bayesian.Cond.Defs
import StatLean.Bayesian.Cond.FinitePartition
import StatLean.Bayesian.Cond.Odds
import StatLean.Bayesian.Experiment.Defs
import StatLean.Bayesian.Experiment.Basic
import StatLean.Bayesian.Dominated.Defs
import StatLean.Bayesian.Dominated.PredictiveDensity
import StatLean.Bayesian.Dominated.PosteriorDensity
import StatLean.Bayesian.Dominated.PosteriorLintegral
import StatLean.Bayesian.Sufficiency.Defs
import StatLean.Bayesian.Sufficiency.Factorization
import StatLean.Bayesian.Updating.Defs
import StatLean.Bayesian.Updating.IID
import StatLean.Bayesian.Updating.Sequential
import StatLean.Bayesian.Updating.Predictive
import StatLean.Bayesian.GeneralizedBayes.Defs
import StatLean.Bayesian.GeneralizedBayes.Basic
import StatLean.Bayesian.GeneralizedBayes.FlatNormal
import StatLean.Bayesian.Conjugacy.Defs
import StatLean.Bayesian.Conjugacy.Criterion
import StatLean.Bayesian.Conjugacy.ExpFamily
import StatLean.Bayesian.Conjugacy.BetaBinomial
import StatLean.Bayesian.Conjugacy.BetaBernoulli
import StatLean.Bayesian.Conjugacy.GammaPoisson
import StatLean.Bayesian.Conjugacy.NormalNormal
import StatLean.Bayesian.Conjugacy.DirichletMultinomial
import StatLean.Bayesian.ModelChoice.Defs
import StatLean.Bayesian.ModelChoice.Basic
import StatLean.Bayesian.ModelChoice.Testing
import StatLean.Bayesian.ModelChoice.CredibleSet
import StatLean.Bayesian.MCMC.Defs
import StatLean.Bayesian.MCMC.MetropolisHastings
import StatLean.Bayesian.MCMC.Gibbs
import StatLean.Bayesian.MCMC.RaoBlackwell
import StatLean.Bayesian.Decision.Defs
import StatLean.Bayesian.Decision.BayesEstimator
import StatLean.Bayesian.Decision.SquaredLoss
import StatLean.Bayesian.Decision.ZeroOneLoss
import StatLean.Bayesian.Decision.Minimax
import StatLean.Bayesian.Hierarchical.Defs
import StatLean.Bayesian.Hierarchical.Decomposition
import StatLean.Bayesian.Hierarchical.Tower
import StatLean.Bayesian.Hierarchical.Exchangeable
import StatLean.Bayesian.Hierarchical.NormalHier
import StatLean.Bayesian.Hierarchical.Shrinkage
import StatLean.Bayesian.Hierarchical.Gibbs
import StatLean.Bayesian.EmpiricalBayes.Defs
import StatLean.Bayesian.EmpiricalBayes.Parametric
import StatLean.Bayesian.EmpiricalBayes.Robbins
import StatLean.Bayesian.EmpiricalBayes.Tweedie
import StatLean.Bayesian.EmpiricalBayes.Compound
import StatLean.Bayesian.EmpiricalBayes.LocalFDR
import StatLean.Bayesian.EmpiricalBayes.NPMLE
import StatLean.Bayesian.ForMathlib.LaplaceDist
import StatLean.Bayesian.ForMathlib.GammaBounds
import StatLean.Bayesian.ForMathlib.BindWithDensity
import StatLean.Bayesian.ForMathlib.PiLintegralFintype
import StatLean.Bayesian.ForMathlib.GaussianShift
import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
import StatLean.Bayesian.DirichletLaplace.Defs
import StatLean.Bayesian.DirichletLaplace.MarginalDensity
import StatLean.Bayesian.DirichletLaplace.DensityBounds
import StatLean.Bayesian.DirichletLaplace.PriorDensityBounds
import StatLean.Bayesian.DirichletLaplace.PriorSmallBall
import StatLean.Bayesian.DirichletLaplace.NormalMeansModel
import StatLean.Bayesian.DirichletLaplace.DenominatorLowerBound
import StatLean.Bayesian.DirichletLaplace.GaussianTests
import StatLean.Bayesian.DirichletLaplace.TestingBound
import StatLean.Bayesian.DirichletLaplace.CoveringNets
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
import StatLean.Bayesian.DirichletLaplace.CompressEngine
import StatLean.Bayesian.DirichletLaplace.ShellDecomposition
import StatLean.Bayesian.DirichletLaplace.PriorMassRatio
import StatLean.Bayesian.DirichletLaplace.Theorem34
import StatLean.Bayesian.DirichletLaplace.Theorem31

/-!
# Bayesian — area umbrella

Bayesian statistics: the Bayesian machine (prior, likelihood, joint, marginal, posterior,
predictive), Bayes' theorem in finite and dominated form, sufficiency and the likelihood
principle, iid/sequential updating and the posterior predictive, conjugate families (exponential
families, Beta–Binomial, Gamma–Poisson, Normal–Normal, Dirichlet–Multinomial — with the Dirichlet
and Multinomial distributions built here), generalized Bayes for improper priors, Bayesian
testing/model choice/credible sets, correctness of finite-state MCMC (Metropolis–Hastings, Gibbs),
the Bayes-decision-theoretic bridge to minimaxity, and — in the hierarchical and empirical-Bayes
layer — two-level models with their posterior tower/mixture decompositions, normal partial pooling,
shrinkage optimality, parametric and nonparametric empirical Bayes (Robbins, Tweedie), and local
false discovery rate.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Chapters 1–7, Chapter 10 (hierarchical and empirical Bayes), and
Appendix A. The local false discovery rate and Tweedie's formula are not in Robert; they follow
B. Efron, *Large-Scale Inference*, Cambridge University Press, 2010. Tag token `Robert §X.Y` in
declaration docstrings.

**Proof formalization notes.** The area builds a textbook-facing layer on top of Mathlib's pinned
probability infrastructure — `ProbabilityTheory.cond`, the posterior kernel `κ†μ` and its
disintegration, `condDistrib`, the decision-risk framework `avgRisk`/`bayesRisk`/`minimaxRisk`,
kernel invariance/reversibility, and the Beta/Gamma/Gaussian/Poisson/Binomial distributions.
Pinned results are imported and given textbook-facing aliases; results not in the pin (the
Bayes-estimator layer, the conjugacy engine and instances, the Dirichlet and Multinomial
distributions, MCMC kernels, the minimax bridge) are formalized here from Robert — never copied
from external Lean sources.

* **Conditional Bayes** (`Cond/`) — odds and the Bayes factor; law of total probability,
  finite-partition and two-hypothesis Bayes. Robert §1.2, §5.2.
* **Bayesian model** (`Experiment/`) — `BayesExperiment` with joint / predictive / posterior; the
  posterior disintegration of the joint. Robert Definition 1.2.1, §1.4.
* **Dominated Bayes** (`Dominated/`) — predictive density; Bayes' theorem in density form; the
  posterior expectation formula. Robert eq. (1.2.3), §1.4.
* **Sufficiency** (`Sufficiency/`) — statistic-induced experiments; the Fisher–Neyman factorized
  likelihood and posterior reduction; the likelihood principle. Robert §1.3.
* **Updating & prediction** (`Updating/`) — iid product likelihoods, sequential Bayes,
  reparameterization equivariance, and the posterior predictive as a conditional law.
  Robert §1.4, eq. (4.1.5).
* **Conjugacy** (`Conjugacy/`) — the normalization criterion; Diaconis–Ylvisaker conjugacy for
  exponential families; Beta–Binomial (with marginal and Laplace's succession rule),
  Gamma–Poisson, Normal–Normal (with predictive), Dirichlet–Multinomial. Robert §3.3
  (Prop. 3.3.13, Table 3.3.1), §4.2 (Table 4.2.1), Example 1.4.1.
* **Generalized Bayes** (`GeneralizedBayes/`) — posteriors from σ-finite (improper) priors:
  propriety, scale invariance, Bayes-factor scaling, the flat-prior normal model. Robert §1.5.
* **Model choice & testing** (`ModelChoice/`) — posterior model probabilities, marginal-likelihood
  Bayes factors, threshold tests under asymmetric 0–1 loss, point-null mixtures, credible sets.
  Robert eq. (7.2.2), §5.2, Definition 5.5.2.
* **MCMC** (`MCMC/`) — detailed balance and stationarity for Metropolis–Hastings and Gibbs
  kernels; Rao–Blackwellization. Robert §6.3 (Theorem 6.3.1, Lemma 6.3.6).
* **Decision theory** (`Decision/`) — Bayes estimators via posterior-risk minimization
  (Thm 2.3.2); posterior mean under quadratic loss (Prop. 2.5.1); MAP under 0–1 loss
  (Prop. 2.5.7/§4.1.2); randomized-risk linearity and the constant-risk/least-favorable route to
  minimaxity (Lemma 2.4.13). The `ForMathlib/` files hold the pin-agnostic bricks (finite product
  densities, the iid and diagonal product kernels, kernel mixtures, the spatial derivative of the
  Gaussian density, and the Multinomial and Dirichlet distributions).
* **Hierarchical Bayes** (`Hierarchical/`) — the `HierBayesExperiment` interface (hyperprior →
  prior kernel → likelihood); the marginal prior, hyperposterior, and conditional posteriors; the
  posterior tower and mixture decompositions; conditional-iid exchangeability; the normal one-way
  hierarchy with partial pooling; linear-shrinkage and James–Stein risk; hierarchical Gibbs.
  Robert §10.1–10.3, Note 2.8.2.
* **Empirical Bayes** (`EmpiricalBayes/`) — the mixture density and marginal likelihood; parametric
  empirical Bayes for the normal random-effects model; Robbins's nonparametric Poisson rule;
  Tweedie's formula; the two-groups model and local false discovery rate; the NPMLE and its
  finite-support geometry. Robert §10.4; Efron, *Large-Scale Inference* (2010); Robbins (1956).

**Bibliographic comments.** The subject runs from Bayes (1763, published by R. Price) and
Laplace's "probability of causes" (1774) through Jeffreys's *Theory of Probability* (1939) — the
first modern treatise — to the decision-theoretic synthesis of Wald (*Statistical Decision
Functions*, 1950) and Savage (*The Foundations of Statistics*, 1954). Conjugate priors originate
with Raiffa and Schlaifer (*Applied Statistical Decision Theory*, 1961) and were characterized for
exponential families by Diaconis and Ylvisaker (*Ann. Statist.* 7 (1979), 269–281); the MCMC
material rests on Metropolis et al. (1953), Hastings (1970), Geman and Geman (1984), and Gelfand
and Smith (1990). Hierarchical priors are due to Good (1965) and Lindley and Smith (*J. Roy.
Statist. Soc. Ser. B* 34 (1972), 1–41); empirical Bayes to Robbins (1956), with the Stein effect
(Stein 1956; James and Stein 1961) as its decision-theoretic driver, the nonparametric MLE geometry
to Lindsay (1983), and the modern large-scale-inference synthesis (two-groups model, local FDR,
Tweedie's formula) to Efron (*Large-Scale Inference*, 2010). Robert's book is the decision-theoretic
synthesis this area follows; his §1.8, §2.8, §3.8 and §10.6 Notes survey the history in detail.
-/
