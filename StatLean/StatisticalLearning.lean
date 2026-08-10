import StatLean.StatisticalLearning.Core.Defs
import StatLean.StatisticalLearning.Core.SampleLaw
import StatLean.StatisticalLearning.Core.ERM
import StatLean.StatisticalLearning.FiniteClass.UniformConvergence
import StatLean.StatisticalLearning.FiniteClass.AgnosticPAC
import StatLean.StatisticalLearning.FiniteClass.RealizablePAC
import StatLean.StatisticalLearning.Rademacher.Defs
import StatLean.StatisticalLearning.Rademacher.Structural
import StatLean.StatisticalLearning.Rademacher.Contraction
import StatLean.StatisticalLearning.Rademacher.Symmetrization
import StatLean.StatisticalLearning.Rademacher.Generalization
import StatLean.StatisticalLearning.VC.Bridge
import StatLean.StatisticalLearning.VC.AgnosticPAC
import StatLean.StatisticalLearning.Stability.Defs
import StatLean.StatisticalLearning.Stability.ReplaceOne
import StatLean.StatisticalLearning.Stability.Generalization
import StatLean.StatisticalLearning.Stability.RegularizedERM
import StatLean.StatisticalLearning.PACBayes.Defs
import StatLean.StatisticalLearning.PACBayes.ChangeOfMeasure
import StatLean.StatisticalLearning.PACBayes.Generalization

/-!
# StatisticalLearning

Statistical learning theory — the formal mathematical theory of why
data-dependent predictors generalize. Reference: Shalev-Shwartz & Ben-David,
*Understanding Machine Learning* (Cambridge, 2014) (`SSBD §X.Y` in tags).

* `Core/` — risk, empirical risk, ERM predicates, `ε`-representative samples,
  PAC/uniform-convergence learnability (SSBD Ch. 2–4).
* `FiniteClass/` — finite classes: uniform convergence, agnostic PAC,
  realizable PAC (SSBD Cor. 2.3, 3.2, 4.6).
* `Rademacher/` — Rademacher complexity: Massart, contraction,
  symmetrization, generalization bounds (SSBD Ch. 26).
* `VC/` — the agnostic upper bound of the Fundamental Theorem via the
  set-class VC machinery of `ConcentrationInequalities/VC/` (SSBD Ch. 6, 28).
* `Stability/` — replace-one stability, stable-rules-do-not-overfit, Tikhonov
  regularization (SSBD Ch. 13).
* `PACBayes/` — change of measure and the PAC-Bayes bound (SSBD Ch. 31).

Concentration machinery is imported from `StatLean.ConcentrationInequalities`
— never re-proven here.
-/
