import StatLean.Bayesian.Cond.Defs
import StatLean.Bayesian.Cond.FinitePartition
import StatLean.Bayesian.Cond.Odds
import StatLean.Bayesian.Experiment.Defs
import StatLean.Bayesian.Experiment.Basic
import StatLean.Bayesian.Dominated.Defs
import StatLean.Bayesian.Dominated.PredictiveDensity
import StatLean.Bayesian.Dominated.PosteriorDensity
import StatLean.Bayesian.Dominated.PosteriorLintegral
import StatLean.Bayesian.Decision.Defs
import StatLean.Bayesian.Decision.BayesEstimator
import StatLean.Bayesian.Decision.SquaredLoss
import StatLean.Bayesian.Decision.ZeroOneLoss

/-!
# Bayesian — area umbrella

Bayesian statistics, formalized from Christian P. Robert, *The Bayesian Choice: From
Decision-Theoretic Foundations to Computational Implementation*, 2nd ed. (Springer, 2007).
Tag token `Robert §X.Y`. This area builds a textbook-facing Bayesian layer on top of Mathlib's
pinned probability infrastructure (`ProbabilityTheory.cond`, the posterior kernel `κ†μ`, and the
decision-risk framework `avgRisk` / `bayesRisk`); results not in the pin are formalized here from
Robert, never copied from external Lean sources.

* **Conditional Bayes** (`Cond/`) — prior/posterior odds and the Bayes factor (`Cond.Defs`); the
  law of total probability, finite-partition Bayes, and two-hypothesis Bayes (`Cond.FinitePartition`);
  posterior odds = prior odds × Bayes factor and its inversion (`Cond.Odds`). Robert §1.2, §5.2.
* **Bayesian model** (`Experiment/`) — `BayesExperiment` (prior + likelihood kernel) with joint /
  predictive / posterior (`Experiment.Defs`); the posterior disintegration of the joint
  (`Experiment.Basic`). Robert §1.2 Definition 1.2.1, §1.4.
* **Dominated Bayes** (`Dominated/`) — predictive density, posterior density, Bayes kernel
  (`Dominated.Defs`); the marginal-density identity and its regularity (`Dominated.PredictiveDensity`);
  Bayes' theorem in dominated form (`Dominated.PosteriorDensity`); the posterior expectation formula
  (`Dominated.PosteriorLintegral`). Robert §1.2 eq. (1.2.3), §1.4.
* **Decision theory** (`Decision/`) — `IsBayesEstimator`, posterior risk, the canonical losses, and
  the posterior mean / mode (`Decision.Defs`); Robert's Theorem 2.3.2 (average risk = integrated
  posterior loss; posterior-risk argmin ⇒ Bayes) formalized from scratch (`Decision.BayesEstimator`);
  the posterior mean is Bayes under quadratic loss (`Decision.SquaredLoss`, Prop. 2.5.1); the
  posterior mode (MAP) is Bayes under 0–1 loss on a finite parameter space (`Decision.ZeroOneLoss`,
  Prop. 2.5.7 / §4.1.2).
-/
