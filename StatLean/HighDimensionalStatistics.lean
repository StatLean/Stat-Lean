import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.HighDimensionalStatistics.LinearModel.Defs
import StatLean.HighDimensionalStatistics.Lasso.Defs
import StatLean.HighDimensionalStatistics.Lasso.DeterministicRate
import StatLean.HighDimensionalStatistics.Lasso.RandomNoise
import StatLean.HighDimensionalStatistics.OLS.MSEExpectation

/-!
# HighDimensionalStatistics — area umbrella

OLS mean-squared-error and Lasso statistical rates, formalized from Lu,
*Big Data Analysis*, ch. 5 and ch. 8. Consumes the `ConcentrationInequalities`
sub-Gaussian/maximal bricks for the noise bounds. Modules are imported above as
each lands.
-/
