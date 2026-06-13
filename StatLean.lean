import StatLean.AsymptoticStatistics
import StatLean.ConcentrationInequalities
import StatLean.Optimization

/-!
# StatLean

Root module of the StatLean library: a Lean 4 formalization of statistical
theory, organized into per-area sublibraries.

* `StatLean.AsymptoticStatistics` — asymptotic statistics (van der Vaart).
* `StatLean.ConcentrationInequalities` — sub-Gaussian / sub-exponential / Bernstein
  / maximal inequalities (Lu, *Big Data Analysis* ch. 2–4).
* `StatLean.Optimization` — convex optimization: subgradients, gradient descent,
  Frank–Wolfe, proximal / accelerated proximal gradient (Lu, *Big Data Analysis*
  ch. 10–12).

Per-area umbrellas are imported above as each area lands.
-/
