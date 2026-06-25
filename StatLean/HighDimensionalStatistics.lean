import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.HighDimensionalStatistics.ForMathlib.TopK
import StatLean.HighDimensionalStatistics.LinearModel.Defs
import StatLean.HighDimensionalStatistics.Lasso.Defs
import StatLean.HighDimensionalStatistics.Lasso.DeterministicRate
import StatLean.HighDimensionalStatistics.Lasso.RandomNoise
import StatLean.HighDimensionalStatistics.OLS.MSEExpectation
import StatLean.HighDimensionalStatistics.OLS.MSEHighProb
import StatLean.HighDimensionalStatistics.CompressedSensing.Defs
import StatLean.HighDimensionalStatistics.CompressedSensing.BasisPursuit
import StatLean.HighDimensionalStatistics.CompressedSensing.ConeTheorem
import StatLean.HighDimensionalStatistics.CompressedSensing.RIPRecovery
import StatLean.HighDimensionalStatistics.CompressedSensing.GaussianChiSquared
import StatLean.HighDimensionalStatistics.CompressedSensing.RandomRIP
import StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
import StatLean.HighDimensionalStatistics.ForMathlib.GramMatrix
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Defs
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DualCertificate
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Theorem7_21
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Corollary7_22

/-!
# HighDimensionalStatistics — area umbrella

OLS mean-squared-error, Lasso statistical rates, and compressed sensing,
formalized from Lu, *Big Data Analysis*, ch. 5, 6, 7 and 8. Consumes the
`ConcentrationInequalities` sub-Gaussian / sub-exponential / covering bricks and
the `AsymptoticStatistics` Gaussian-MGF bricks for the noise and random-matrix
bounds. Compressed sensing (ch. 6–7): the cone theorem (`thm:cone`), perfect
recovery under RIP (`thm:rip`), and the random-Gaussian RIP guarantee
(`thm:3s-rip`). Modules are imported above as each lands.
-/
