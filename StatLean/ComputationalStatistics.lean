import StatLean.ComputationalStatistics.ForMathlib.PiMoments
import StatLean.ComputationalStatistics.ForMathlib.PiMarginal
import StatLean.ComputationalStatistics.Core.Defs
import StatLean.ComputationalStatistics.Core.EmpiricalMeasure
import StatLean.ComputationalStatistics.MonteCarlo.Estimation
import StatLean.ComputationalStatistics.MonteCarlo.ImportanceSampling
import StatLean.ComputationalStatistics.MonteCarlo.RejectionSampling
import StatLean.ComputationalStatistics.Resampling.CategoricalCounts
import StatLean.ComputationalStatistics.Resampling.MultinomialMoments
import StatLean.ComputationalStatistics.Resampling.ParticleResampling
import StatLean.ComputationalStatistics.Resampling.BootstrapMoments
import StatLean.ComputationalStatistics.Resampling.Jackknife
import StatLean.ComputationalStatistics.Resampling.JackknifeBias
import StatLean.ComputationalStatistics.Partitioning.Holdout
import StatLean.ComputationalStatistics.Partitioning.KFold

/-!
# StatLean.ComputationalStatistics — area umbrella

The mathematical correctness of sampling and resampling algorithms: empirical,
weighted and categorical measures as the common substrate; ordinary Monte
Carlo estimation (unbiasedness, `σ²/n` variance, MSE, strong consistency);
importance sampling (the change-of-measure identity, estimator moments, the
optimal importance function); rejection sampling (acceptance probability
`1/c`, the accepted draw has exactly the target law); multinomial resampling
of weighted particles (the SMC resampling brick); finite-sample bootstrap
identities (Efron's multinomial resampling counts, conditional mean/variance
of the bootstrap mean, ideal-bootstrap bias correction); the jackknife
(pseudovalues, Tukey's variance estimator, exact first-order bias
annihilation); and holdout / K-fold / leave-one-out cross validation
(conditional unbiasedness for the trained rule's risk).  Reference: J. E.
Gentle, *Elements of Computational Statistics*, Springer, 2002 (`ECS §X.Y`
in tags).

Deliberately *not* here, because other areas already formalize it: MCMC
correctness (`StatLean.Bayesian.MCMC`), Markov-chain ergodicity
(`StatLean.TimeSeries` `ForMathlib/Markov`), permutation/randomization tests
(`StatLean.HypothesisTesting` Randomization; `StatLean.CausalInference`
Fisher), simple random sampling (`StatLean.ExperimentalDesign`), bootstrap
asymptotics (`StatLean.HypothesisTesting` Bootstrap), and inverse-CDF
sampling (`StatLean.HypothesisTesting` `ForMathlib/QuantileFunction`).

Laptop-only file: edited by the laptop session at wave merges.
-/
