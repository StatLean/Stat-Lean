import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
import StatLean.RobustStatistics.Core.Contamination
import StatLean.RobustStatistics.Core.Equivariance
import StatLean.RobustStatistics.Core.InfluenceFunction
import StatLean.RobustStatistics.Core.Bias
import StatLean.RobustStatistics.Core.BreakdownPoint
import StatLean.RobustStatistics.LocationScale.Huber
import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.RobustStatistics.LocationScale.Median
import StatLean.RobustStatistics.LocationScale.MedianBreakdown
import StatLean.RobustStatistics.LocationScale.MLocation
import StatLean.RobustStatistics.LocationScale.MAD
import StatLean.RobustStatistics.LocationScale.TrimmedMean
import StatLean.RobustStatistics.MEstimation.MLocationFunctional
import StatLean.RobustStatistics.MEstimation.Influence
import StatLean.RobustStatistics.MEstimation.AsymptoticBreakdown
import StatLean.RobustStatistics.MEstimation.Asymptotics
import StatLean.RobustStatistics.Regression.MRegression
import StatLean.RobustStatistics.Multivariate.AffineEquivariance

/-!
# StatLean.RobustStatistics — area umbrella

Robust statistics: measuring the sensitivity of estimators to contamination, and the
estimators built to withstand it. The organizing spine is

contamination → equivariance → statistical functionals →
{influence function, breakdown point, maximum bias} → robust estimators.

* `ForMathlib/` — `OrderStatPerturb` (order statistics under affine maps and coordinate
  replacement; the combinatorial engine of finite-sample breakdown).
* `Core/` — the robustness diagnostics: `Contamination` (the ε-mixture `(1-ε)P + εQ` and
  gross-error neighbourhoods), `Equivariance` (location/scale/dispersion predicates),
  `InfluenceFunction` (one-sided contamination derivative), `Bias` (bounded contamination
  bias), `BreakdownPoint` (finite-sample replacement breakdown, maximal-breakdown bound
  for location-equivariant estimators).
* `LocationScale/` — the concrete estimators: `Huber` (loss and clipped score), `Mean`
  (the fragile pole: unbounded IF, breakdown count 0, infinite maximum bias), `Median` and
  `MedianBreakdown` (the robust pole: breakdown count `⌊(n-1)/2⌋`, the equivariant
  maximum), `MLocation` (M-estimates: objective ↔ estimating equation), `MAD`,
  `TrimmedMean`.
* `MEstimation/` — the population theory: `MLocationFunctional` (roots of
  `E_P ψ(x-θ) = 0`), `Influence` (the flagship IF formula `ψ(x₀-θ₀)/A`; bounded score ⟹
  bounded influence), `AsymptoticBreakdown` (`ε* = min(k₁,k₂)/(k₁+k₂)`, `1/2` for Huber),
  `Asymptotics` (consistency and √n-normality by reuse of
  `StatLean/AsymptoticStatistics` Z-estimation theory).
* `Regression/` — `MRegression` (objective, M-normal equations, Huber convexity,
  regression equivariance, the leverage counterexample).
* `Multivariate/` — `AffineEquivariance` (location/scatter equivariance interface; mean
  and covariance sanity checks).

**Scope.** Round 1: measuring robustness (MMY ch. 2–3) plus the reuse-driven asymptotics
(MMY ch. 10) and the foundational regression/multivariate layer (MMY §4.4, §6.17.1).
Deferred: minimax bias/variance optimality (Huber 1964, MMY §3.5), scale M-estimators and
MAD breakdown, S/MM/LTS regression, high-breakdown multivariate estimators.

**Relation to other areas.** Imports `StatLean.MultipleTesting.ForMathlib.OrderStatistics`
(order statistics), `StatLean.PointEstimation.Equivariance.Defs` (finite-sample
equivariance), and the `StatLean.AsymptoticStatistics` consistency/empirical-process
layers (Z-estimator asymptotics); the DAG direction is strictly downward into
RobustStatistics.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY §X.Y` in tags.)

Laptop-only file: edited by the laptop session at wave merges.
-/
