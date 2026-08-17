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
import StatLean.RobustStatistics.Multivariate.BallMoM
import StatLean.RobustStatistics.HeavyTails.EmpiricalMeanBaseline
import StatLean.RobustStatistics.HeavyTails.MedianOfMeans
import StatLean.RobustStatistics.HeavyTails.Catoni
import StatLean.RobustStatistics.HeavyTails.TrimmedMean
import StatLean.RobustStatistics.HeavyTails.DeviationLowerBound
import StatLean.RobustStatistics.Scale.MScale
import StatLean.RobustStatistics.Scale.DispersionBreakdown
import StatLean.RobustStatistics.MaxBias.MaxBiasLocation
import StatLean.RobustStatistics.MaxBias.MedianMinimaxBias

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
  regression equivariance, the leverage counterexample, and regression quantiles —
  the check loss and the Koenker–Bassett regression α-quantile).
* `Multivariate/` — `AffineEquivariance` (location/scatter equivariance interface; mean
  and covariance sanity checks); `BallMoM` (the dimension-free minimal-radius-ball
  median-of-means, LM Proposition 1).
* `HeavyTails/` — modern sub-Gaussian mean estimation under two moments (LM 2019):
  `EmpiricalMeanBaseline` (the Chebyshev baseline), `MedianOfMeans` (LM Thm 2),
  `Catoni` (LM Thm 5), `TrimmedMean` (LM Thm 6, two-sample quantile trimming),
  `DeviationLowerBound` (LM Thm 1 — no estimator beats σ√(log(1/δ)/n)).
* `Scale/` — `MScale` (scale M-functionals, the log-scale reduction, breakdown point
  min(δ, 1−δ)); `DispersionBreakdown` (implosion-aware finite-sample breakdown: SD = 0,
  MAD → 1/2).
* `MaxBias/` — `MaxBiasLocation` (the sharp maximum-bias bound b_ε and the median's
  quantile formula, MMY (3.66)–(3.68)); `MedianMinimaxBias` (Huber's minimax-bias
  property of the median, MMY §3.8.5).

**Scope.** Round 1: measuring robustness (MMY ch. 2–3) plus the reuse-driven asymptotics
(MMY ch. 10) and the foundational regression/multivariate layer (MMY §4.4, §6.17.1).
Round 2 (breadth + modern): sub-Gaussian mean estimation under heavy tails (LM 2019 —
median-of-means, Catoni, trimmed mean, the deviation lower bound, the dimension-free
multivariate ball-MoM), scale M-functionals and dispersion breakdown, maximum-bias
theory with the median's minimax-bias property, and regression quantiles.
Deferred: LM Thm 3 (1+α moments) and Thm 7 (multiple-δ impossibility, after
Devroye–Lerasle–Lugosi–Oliveira 2016), the Catoni–Giulini thresholding estimator and
median-of-means tournaments (LM §3.3–3.4), the geometric median-of-means (Minsker
2015), contamination-robust trimmed means (Lugosi–Mendelson 2021), the median influence
function, Hampel optimality (MMY §3.8.6–3.8.7), S/MM/LTS regression, high-breakdown
multivariate estimators.

**Relation to other areas.** Imports `StatLean.MultipleTesting.ForMathlib.OrderStatistics`
(order statistics), `StatLean.PointEstimation.Equivariance.Defs` (finite-sample
equivariance), and the `StatLean.AsymptoticStatistics` consistency/empirical-process
layers (Z-estimator asymptotics); the DAG direction is strictly downward into
RobustStatistics.

**References.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019 (`MMY §X.Y` in
tags) — the classical spine; G. Lugosi and S. Mendelson, *Mean estimation and
regression under heavy-tailed distributions — a survey*, Found. Comput. Math. (2019),
arXiv:1906.04280v1 (`LM Thm N` / `LM (x.y)` in tags) — the modern spine.

Laptop-only file: edited by the laptop session at wave merges.
-/
