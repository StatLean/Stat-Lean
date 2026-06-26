# Batch 8 — Candès STAT 300C — status

**STATE:** **Phase A complete (6/6 0-sorry)**; Phase B underway. Merged: U-EV, U-EMPCDF, U-GAUSS,
U-GAMMA, U-BHD (T4), U-EB (T8) [all 0-sorry], U-CHISQ [4 lemmas real; law=1 debt]. Closing: U-CONF,
U-CHI. Remaining: U-REVMG → U-BHM/U-STO; U-MASSART → U-KS; U-HC; + U-CHISQ-LAW follow-up. Integration
branch `mt/batch8` (off `main` @ `f043f2a`). Reference: Candès STAT 300C. See `outline.md`.

**API correction:** `ProbabilityTheory.Exchangeable` is **NOT** in Mathlib v4.29.1 (loogle 0 hits —
the Batch-8 exploration agent was wrong). U-RANK / U-CONF must **define exchangeability ourselves**
(permutation-invariance of the joint law, `Measure.map (S∘σ) = Measure.map S`) and prove
rank-uniformity from that symmetry. `IdentDistrib` + `iIndepFun` are available for the iid pieces.

**Pipeline validated (2026-06-26):** U-EV vertical slice stub-gated GREEN on cluster —
`StatLean.MultipleTesting.EValues.Conversion` builds (2421 jobs, exit 0), `EValues.Defs` 0-sorry,
`EValues.Conversion` exactly 2 named sorries. Cluster worktree + sbatch + shared-Mathlib cache all
confirmed working. Worktree-add must precede `--worktree` builds; run cluster wrappers from inside
`Stat-Lean/` (cwd resets to the non-repo parent otherwise).

Protocol per unit (CLAUDE.md §10): Frame → Stubs (laptop) → Stub gate (cluster, green-with-sorries)
→ Proof closure (`lean-fasrc-cluster-claude`) → Verification gate (laptop: fresh build + sorry
inventory + diff ⊆ touch-set, no laundering) → Merge `--no-ff` into `mt/batch8` + umbrella update.

## Unit ledger

Diff: ◐ easy · ● moderate · ◆ hard · ◆◆ research-hard. Status: stub / gated / proving / ✅ real / debt.

| Unit | Branch | File(s) | Dep | Diff | Status |
|---|---|---|---|---|---|
| U-EV | `mt/evalues` | `EValues/{Defs,Conversion}` | PValues | ◐ | ✅ real (merged, 0-sorry) |
| U-GAUSS | `mt/gauss-moments` | `ForMathlib/GaussianMoments` | — | ● | ✅ real (merged, 0-sorry) |
| U-GAMMA | `mt/gamma-moments` | `ForMathlib/GammaMoments` | — | ◆ | ✅ real (merged, 0-sorry, incl. MGF) |
| U-EMPCDF | `mt/empirical-cdf` | `ForMathlib/EmpiricalCDF` | — | ● | ✅ real (merged, 0-sorry) |
| U-RANK | `mt/rank-uniform` | `ForMathlib/RankUniform` | — | ● | ✅ real (merged, 0-sorry) |
| U-BHD | `mt/bh-dependent` | `BHDependence` | FDP,PValues,harmonic | ◆ | ✅ real (merged, 0-sorry) — T4 |
| U-CHISQ | `mt/chisquared-dist` | `ForMathlib/ChiSquared` (+GaussianSquareMGF) | GAUSS,GAMMA | ◆ | ✅ FULLY real (merged, 0-sorry incl. exact law) |
| U-EB | `mt/empirical-bayes` | `EmpiricalBayes/BayesRisk` | gaussian 2nd-moment | ● | ✅ real (merged, 0-sorry) — T8 |
| U-CONF | `mt/conformal` | `Conformal/Coverage` | RANK | ● | ✅ real (merged, 0-sorry) — T7 |
| U-CHI | `mt/chisq-test` | `ChiSquaredTest/Distribution` | GAUSS,CHISQ | ● | ✅ real (merged, 0-sorry) |
| U-REVMG | `mt/reverse-martingale` | `ForMathlib/ReverseMartingale` | EMPCDF,OptStop | ◆ | todo |
| U-BHM | `mt/bh-martingale` | `BHMartingale` | BH (leave-one-out) | ◆ | ✅ real (merged, 0-sorry) — T5 |
| U-STO | `mt/storey` | `Storey` | reverse-MG,BinomialRatio | ◆ | ⚠ stated + 2 documented debts (reverse-MG OST core) — T6 |
| U-MASSART | `mt/massart` | `ForMathlib/EmpiricalProcessSup` | EMPCDF | ◆◆ | ✅ union bound real (merged); **sharp = 1 debt** |
| U-KS | `mt/ks-test` | `GoodnessOfFit/KolmogorovSmirnov` | EMPCDF,MASSART | ● | ✅ real (merged, 0-sorry) |
| U-HC | `mt/higher-criticism` | `GoodnessOfFit/HigherCriticism` | EMPCDF | ◆◆ | ⚠ boundary+statistic real (0-sorry); full theorem honestly deferred |

Concept `Defs.lean` (laptop-only, no sorry): `EValues/Defs` ✓ written;
`ChiSquaredTest/Defs`, `GoodnessOfFit/Defs`, `EmpiricalBayes/Defs`, `Conformal/Defs` — todo.

## Waves (dependency-respecting, ≤3 concurrent)

- Wave 0 ✅ · A1 ✅ (GAUSS·GAMMA·EMPCDF) · A2 ✅ (EV·BHD; **RANK left**) · B1 partial (EB ✅; **CHISQ·CONF left**)
- **Integration GREEN (2026-06-26):** full `StatLean.MultipleTesting` umbrella builds 0-sorry with all
  6 merged units (EV, EMPCDF, GAUSS, GAMMA, BHD/T4, EB/T8) + existing BH/Holm/Knockoff area.
- Remaining: **A2** RANK · **B1** CHISQ, CONF · **B2** REVMG · **B3** BHM, STO · **C1** MASSART · **C2** KS, HC.
  RANK/CONF need a self-defined `Exchangeable`; REVMG is the BH-martingale/Storey core; MASSART/HC are
  research-hard (documented-`sorry` fallbacks per the plan).

## Pipeline de-risk (done)

U-EV taken end-to-end first to validate the pipeline; the full per-unit protocol (stub → cluster
stub-gate → cluster-claude closure → laptop verification gate → `--no-ff` merge → worktree cleanup)
has now run cleanly 6×, including a caught soundness bug, an SSH-expiry recovery (`fasrc-fix`), and
two orphaned-closure poll-harvests.

## Lessons / gotchas
- **Bochner `∫ f ∂μ ≤ C` is unsound for "expectation ≤ C" predicates.** Mathlib's Bochner integral
  of a *non-integrable* function is `0` (`integral_undef`), so a nonneg non-integrable `f` satisfies
  `∫ f ≤ C` vacuously with infinite true expectation. Use the **lintegral** `∫⁻ ofReal(f) ∂μ ≤ C`
  (genuine expectation for nonneg `f`; bound forces finiteness ⇒ integrability). Caught by the
  cluster gate on U-EV — `IsEVariable.expectation_le_one` switched Bochner→lintegral; both
  conversion theorems were false under the Bochner form (counterexample `E ω = 2/ω` on `(0,1)`).

## Residual named debts (final)
- ✅ **χ² exact law `map_sum_sq_eq_chiSquared` — RETIRED** (closed by U-CHISQ-LAW via the complexMGF
  route; full chi-squared infrastructure now 0-sorry).
- **`massart_inequality`** (`ForMathlib/EmpiricalProcessSup.lean`) — the *sharp* DKW constant
  `2·e^{−2nu²}` (Massart 1990 reflection argument, Mathlib-absent). The union-bound `n·e^{−2nu²}` is
  proved real and is what U-KS consumes; the sharp constant is the only outstanding goodness-of-fit debt.
- **U-STO (`Storey.lean`), 2 sorries** — `storey_reverseMG_ost` (the backwards-martingale optional
  stopping; Mathlib lacks continuous-time backwards MGs — needs the discrete uniform-null reformulation,
  a self-contained development) and `storey_fdr_le` (the FDRhat-attainment + joint-factor-OST + null-count
  `Bin(n₀,½)` assembly atop it). The FDP→counting-process reduction is proved real.
- **U-HC (`GoodnessOfFit/HigherCriticism.lean`)** — `rhoStar` boundary + `hcStat` formalized (boundary
  properties closing on `mt/higher-criticism`); the full Donoho–Jin detection theorem is **honestly
  deferred in prose, NOT laundered**. *Correction (user):* the project HAS Donsker
  (`AsymptoticStatistics.EmpiricalProcess.IsPDonsker` + `isPDonsker_of_finite_bracketing_entropy_integral`),
  so the H₀ empirical-process convergence is reachable; remaining gaps are the empirical-process LIL
  (`√(2 log log n)` calibration) and the H₁ sparse-mixture large deviations.

## Book-vs-Lean constants
(populated as units land.)
