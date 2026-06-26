import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import StatLean.MultipleTesting.EValues.Defs
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.ForMathlib.OrderStatistics
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.ForMathlib.BinomialRatio
import StatLean.MultipleTesting.ForMathlib.SymmetricCondExp
import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.MultipleTesting.ForMathlib.GaussianMoments
import StatLean.MultipleTesting.ForMathlib.GammaMoments
import StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.MultipleTesting.ForMathlib.RankUniform
import StatLean.MultipleTesting.ForMathlib.EmpiricalProcessSup
import StatLean.MultipleTesting.BenjaminiHochberg
import StatLean.MultipleTesting.BHDependence
import StatLean.MultipleTesting.HolmBonferroni
import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.FdpBound
import StatLean.MultipleTesting.Knockoff.Initial
import StatLean.MultipleTesting.Knockoff.Supermartingale
import StatLean.MultipleTesting.Knockoff
import StatLean.MultipleTesting.EValues.Conversion
import StatLean.MultipleTesting.EmpiricalBayes.BayesRisk
import StatLean.MultipleTesting.ChiSquaredTest.Distribution
import StatLean.MultipleTesting.Conformal.Coverage

/-!
# MultipleTesting — area umbrella

Multiple hypothesis testing: false discovery rate and family-wise error rate control, formalized
from Lu, *Big Data Analysis* ch. 18–19 (Holm–Bonferroni from Holm 1979):

* **Concepts**: `FDP` / `FDR` / `FWER` (`FDP/Defs.lean`); `SuperUniform` null p-values
  (`PValues/Defs.lean`); `KnockoffScore` (`Knockoff/Defs.lean`).
* **ForMathlib**: order statistics of a real tuple (`OrderStatistics.lean`); the optional
  stopping theorem `thm:optstop` as a supermartingale bridge to Mathlib (`OptionalStopping.lean`);
  the binomial-ratio inequalities (`BinomialRatio.lean`); the exchangeable conditional expectation
  `E[𝟙(σᵢ)|count] = count/k` for i.i.d. fair Bool variables (`SymmetricCondExp.lean`).
* **Benjamini–Hochberg** (§18): `benjamini_hochberg_fdr_le` — `FDR ≤ (N₀/N)·α`.
* **Holm–Bonferroni** (Holm 1979; §17 Bonferroni): `holm_fwer_le`, `bonferroni_fwer_le` —
  `FWER ≤ α`.
* **Knock-off** (§19): `knockoff_fdr_le` — `FDR ≤ α`.

**Batch 8 — Candès STAT 300C** (large-scale inference; this area is the library's catch-all
testing area). Landing incrementally:

* **E-values** (Candès L15, Defs. 3–4, Prop. 3): `IsEVariable` / `IsPVariable`
  (`EValues/Defs.lean`); `isPVariable_inv_of_isEVariable`, `superUniform_inv_of_isEVariable`
  (`EValues/Conversion.lean`) — `1/E` is a (super-uniform) p-value.

Modules are imported above as each lands.
-/
