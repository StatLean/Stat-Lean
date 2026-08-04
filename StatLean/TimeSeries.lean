import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
import StatLean.TimeSeries.ForMathlib.Fourier.FejerKernel
import StatLean.TimeSeries.ForMathlib.Fourier.MeasureFourierCoeff
import StatLean.TimeSeries.ForMathlib.Markov.Chain
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
import StatLean.TimeSeries.Process.Defs
import StatLean.TimeSeries.Process.Stationary
import StatLean.TimeSeries.Process.SecondOrder
import StatLean.TimeSeries.Process.Autocovariance
import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.Mixing.Defs

/-!
# StatLean.TimeSeries — area umbrella

Time series analysis after J. Fan and Q. Yao, *Nonlinear Time Series: Nonparametric and
Parametric Methods*, Springer, 2003 (`FY` in tags). Scope: FY ch. 1 model definitions;
§2.1–§2.4 and §2.6 (skipping §2.1.4, with §2.7 proofs); §3.1–§3.5; §4.1–§4.2.
Roadmap and status: `notes/time_series/` (laptop-local).

Laptop-only file: edited by the laptop session at wave merges.
-/
