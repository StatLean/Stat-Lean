/-!
# StatLean.ExperimentalDesign — area umbrella

Design of experiments and design-based survey sampling in the finite randomisation
model: finite populations, randomization/sampling designs as `PMF`s, completely
randomised and blocked designs, inclusion probabilities and Horvitz–Thompson
estimation, contrast algebra, two-level factorial characters, and the one-way ANOVA
identity.  Reference: R. Mead, *The Design of Experiments: Statistical Principles for
Practical Applications*, Cambridge University Press, 1988 (`Mead §X.Y` in tags);
survey-sampling results follow Horvitz–Thompson (1952) and Cochran (1977).
-/

import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation
import StatLean.ExperimentalDesign.Core.FinitePopulation
import StatLean.ExperimentalDesign.Core.Design
import StatLean.ExperimentalDesign.Core.Contrast
import StatLean.ExperimentalDesign.Core.Stratification
import StatLean.ExperimentalDesign.Randomization.CompleteRandomization
import StatLean.ExperimentalDesign.Randomization.SamplingEquivalence
import StatLean.ExperimentalDesign.Randomization.Blocked
import StatLean.ExperimentalDesign.SurveySampling.InclusionProbability
import StatLean.ExperimentalDesign.SurveySampling.HorvitzThompson
import StatLean.ExperimentalDesign.SurveySampling.SimpleRandomSampling
import StatLean.ExperimentalDesign.Factorial.TwoLevel
import StatLean.ExperimentalDesign.Analysis.OneWayANOVA
import StatLean.ExperimentalDesign.Stratified.ProductDesign
import StatLean.ExperimentalDesign.Stratified.StratifiedEstimator
