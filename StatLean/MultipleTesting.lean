import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.ForMathlib.OrderStatistics
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.BenjaminiHochberg
import StatLean.MultipleTesting.HolmBonferroni
import StatLean.MultipleTesting.Knockoff

/-!
# MultipleTesting — area umbrella

Multiple hypothesis testing: false discovery rate and family-wise error rate control, formalized
from Lu, *Big Data Analysis* ch. 18–19 (Holm–Bonferroni from Holm 1979):

* **Concepts**: `FDP` / `FDR` / `FWER` (`FDP/Defs.lean`); `SuperUniform` null p-values
  (`PValues/Defs.lean`); `KnockoffScore` (`Knockoff/Defs.lean`).
* **ForMathlib**: order statistics of a real tuple (`OrderStatistics.lean`); the optional
  stopping theorem `thm:optstop` as a supermartingale bridge to Mathlib (`OptionalStopping.lean`).
* **Benjamini–Hochberg** (§18): `benjamini_hochberg_fdr_le` — `FDR ≤ (N₀/N)·α`.
* **Holm–Bonferroni** (Holm 1979; §17 Bonferroni): `holm_fwer_le`, `bonferroni_fwer_le` —
  `FWER ≤ α`.
* **Knock-off** (§19): `knockoff_fdr_le` — `FDR ≤ α`.

Modules are imported above as each lands.
-/
