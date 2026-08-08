import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
import StatLean.TimeSeries.ForMathlib.Fourier.FejerKernel
import StatLean.TimeSeries.ForMathlib.Fourier.MeasureFourierCoeff
import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
import StatLean.TimeSeries.ForMathlib.Markov.Chain
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.CondCharFun
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
import StatLean.TimeSeries.Process.Defs
import StatLean.TimeSeries.Process.Stationary
import StatLean.TimeSeries.Process.SecondOrder
import StatLean.TimeSeries.Process.Autocovariance
import StatLean.TimeSeries.Process.LinearProcess
import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.Models.WhiteNoise
import StatLean.TimeSeries.Models.Linear
import StatLean.TimeSeries.Process.PartialAutocorrelation
import StatLean.TimeSeries.Process.SampleACF
import StatLean.TimeSeries.Stationarity.ARMAExistence
import StatLean.TimeSeries.Stationarity.Gaussian
import StatLean.TimeSeries.Stationarity.ARCH
import StatLean.TimeSeries.Spectral.SpectralMeasure
import StatLean.TimeSeries.Spectral.SpectralDensity
import StatLean.TimeSeries.Spectral.LinearFilter
import StatLean.TimeSeries.Spectral.ARMASpectral
import StatLean.TimeSeries.Spectral.DFT
import StatLean.TimeSeries.Spectral.Periodogram
import StatLean.TimeSeries.Spectral.PeriodogramAsymptotics
import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.Mixing.Relations
import StatLean.TimeSeries.Mixing.Inequalities
import StatLean.TimeSeries.Mixing.MarkovBridge
import StatLean.TimeSeries.Mixing.LimitTheorems
import StatLean.TimeSeries.Mixing.KernelRegressionCLT
import StatLean.TimeSeries.ARMA.Prediction
import StatLean.TimeSeries.ARMA.Likelihood
import StatLean.TimeSeries.ARMA.OrderSelection
import StatLean.TimeSeries.ARMA.ScoreAnalysis
import StatLean.TimeSeries.ARMA.Consistency
import StatLean.TimeSeries.ARMA.MLEAsymptotics
import StatLean.TimeSeries.ARMA.Diagnostics
import StatLean.TimeSeries.Threshold.TAR
import StatLean.TimeSeries.Threshold.Estimation
import StatLean.TimeSeries.Threshold.LinearityTest
import StatLean.TimeSeries.GARCH.ARCHBasic
import StatLean.TimeSeries.GARCH.GARCHBasic
import StatLean.TimeSeries.GARCH.Estimation
import StatLean.TimeSeries.GARCH.ARCHTest
import StatLean.TimeSeries.GARCH.StochasticVolatility

/-!
# StatLean.TimeSeries — area umbrella

Time series analysis after J. Fan and Q. Yao, *Nonlinear Time Series: Nonparametric and
Parametric Methods*, Springer, 2003 (`FY` in tags). Scope: FY ch. 1 model definitions;
§2.1–§2.4 and §2.6 (skipping §2.1.4, with §2.7 proofs); §3.1–§3.5; §4.1–§4.2.
Roadmap and status: `notes/time_series/` (laptop-local).

Laptop-only file: edited by the laptop session at wave merges.
-/
