# Batch 8 — Candès STAT 300C — outline

Reference: Candès, *Theory of Statistics* (STAT 300C, 2023) lecture notes,
`ref/Candes_Inference/Lectures2023/*.pdf`. Citation tag in code:
`-- Candès, Theorem/Prop/Def XX, Lecture YY, STAT 300C Notes`.

Integration branch: `mt/batch8` (off `main`). All new code under `StatLean/MultipleTesting/`
(user decision: single area, no new top-level area). Pin: Lean/Mathlib `v4.29.1`.

## Targets (9 results)

| # | Result | Lecture | Disposition |
|---|---|---|---|
| T1 | χ² test under H₀/H₁ (statistic Tₙ=‖Y‖²); exact χ²ₙ law + moments + CLT/power | L02 §2.3 | full, incl. exact law |
| T2 | Massart / Kolmogorov–Smirnov one-sided bound `P(KS⁺≥u)≤2e^{−2nu²}` | L03 §3.3.1 | full attempt (Risk) |
| T3 | Higher-Criticism detection boundary (Donoho–Jin), `ρ*(β)` | L03 §3.3.3 | full attempt (Risk; partial likely) |
| T4 | BH under arbitrary dependence, `FDR ≤ α·Hₙ·n₀/n` | L05 §5.5 / L06 §6.6 | full |
| T5 | BH via (reverse) martingale, `E[FDP(τ_BH)] = q·n₀/n` | L07 §7.2 | full |
| T6 | Storey q-value, `E[FDP(τ)] ≤ q` | L07 §7.4 | full |
| T7 | Conformal coverage, `P(Y_{n+1}∈Ĉ) ≥ 1−α` | L09 §9.6 | full |
| T8 | Empirical-Bayes risk, `R_B = R_MLE·τ²/(τ²+σ²)` | L15 §15.3.3 | full |
| T9 | E-values: e-variable / p-variable defs + `P=1/E` conversion | L15 §15.6.2 | full (easy) |

## Reuse (already in the library)

- `FDP`/`FDR`/`FWER` (`FDP/Defs.lean`); `SuperUniform` (`PValues/Defs.lean`).
- `orderStat`, `orderStat_monotone` (`ForMathlib/OrderStatistics.lean`).
- supermartingale optional-stopping bridge `supermartingale_integral_stoppedValue_le`
  (`ForMathlib/OptionalStopping.lean`); `BinomialRatio.lean`; exchangeable condexp
  `condExp_coord_eq_count_div` (`ForMathlib/SymmetricCondExp.lean`).
- `AsymptoticStatistics/ForMathlib/` Gaussian suite — `GaussianMGF`, `GaussianVarCharFn`,
  `MultivariateGaussianConv`, `PiGaussian` (importable; ForMathlib layer).
- The χ²₁ MGF integral `∫ exp(l x²) dN(0,1) = (1−2l)^{−1/2}` and `map_sum_gaussianReal`
  exist in `HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean` (concept layer —
  cannot import upward; re-derive the reusable bricks into `MultipleTesting/ForMathlib/`).

## Mathlib coverage (verified v4.29.1)

- Direct: `gaussianReal` (mean/var/mgf/charFun), `Measure.conv`, `IndepFun.hasLaw_add`,
  `iIndepFun.mgf_sum`, `harmonic` + `harmonic_le_one_add_log`, `ProbabilityTheory.Exchangeable`,
  Markov `mul_meas_ge_le_integral_of_nonneg`, `condExp_indicator`, `maximal_ineq`, CLT, strong law,
  `BrownianReal` (time-inversion only).
- Absent (build ourselves): chi-squared distribution, Gamma moments, sum-of-squares law,
  empirical CDF, DKW/Massart, Glivenko–Cantelli, backwards martingales, rank-uniformity, quantiles.

## Dependency DAG (new bricks → concept → assembly)

```
GaussianMoments ─┐
GammaMoments ────┴─→ ChiSquared ──→ ChiSquaredTest/Distribution            (T1)
EmpiricalCDF ─────┬─→ ReverseMartingale ─→ BHMartingale (T5), Storey (T6)
                  └─→ EmpiricalProcessSup (Massart) ─→ KolmogorovSmirnov   (T2)
                                                    └─→ HigherCriticism + BrownianBridgeLIL (T3)
RankUniform ─────────→ Conformal/Coverage                                  (T7)
EValues/Defs ────────→ EValues/Conversion                                  (T9)
GaussianMoments ─────→ EmpiricalBayes/BayesRisk                            (T8)
FDP, PValues, harmonic, orderStat ─→ BHDependence                          (T4)
```

## Units (16) — see status.md for the live ledger

Phase A (foundations + easy wins): U-GAUSS, U-GAMMA, U-EMPCDF, U-EV, U-RANK, U-BHD.
Phase B (distributions, conformal, martingale BH): U-CHISQ, U-EB, U-CONF, U-REVMG, U-BHM, U-STO.
Phase C (research-hard): U-MASSART, U-KS, U-HC.

## Constants to watch (book vs provable)

- χ²₁ centered sub-exponential parameter was `α=4` (not book `2`) in the existing CS work;
  the **exact-law** route here is independent of that tail constant.
- Massart constant `2e^{−2nu²}` is the sharp target; fallback ladder may land `2n·e^{−2nu²}`.
- BH-dependence factor `S(n) = Hₙ` (harmonic), `Hₙ ≤ 1 + log n` via `harmonic_le_one_add_log`.
