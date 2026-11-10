import StatLean.ForMathlib.BindCDF
import StatLean.ForMathlib.BindConv
import StatLean.ForMathlib.BindProd
import StatLean.ForMathlib.ENNRealTsum
import StatLean.ForMathlib.PoissonPMF
import StatLean.ForMathlib.UniformPMF

/-!
# Mathlib extensions shared across StatLean areas

* `StatLean.ForMathlib.BindProd` — `Measure.bindProd`, the product of arbitrary measures.
* `StatLean.ForMathlib.BindConv` — `Measure.bindConv`, the convolution of arbitrary measures.
* `StatLean.ForMathlib.BindCDF` — `ProbabilityTheory.bindCDF`, the CDF of an arbitrary real
  measure.
* `StatLean.ForMathlib.ENNRealTsum` — `ENNReal.measurable_tsum`, measurability of countable sums
  in `ℝ≥0∞` for any σ-algebra on the domain.
* `StatLean.ForMathlib.UniformPMF` — `PMF.uniformOn` and `PMF.uniform`, uniform probability mass
  functions on finite sets.
* `StatLean.ForMathlib.PoissonPMF` — `ProbabilityTheory.poissonPMFReal`, the real-valued Poisson
  mass function.
-/
