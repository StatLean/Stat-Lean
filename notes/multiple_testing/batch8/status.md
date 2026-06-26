# Batch 8 — Candès STAT 300C — status

**STATE: BATCH 8 COMPLETE + debt-closing pass done** — all targets on `mt/batch8` (off `main` @
`f043f2a`); `StatLean.MultipleTesting` builds with **7 precisely-isolated named-crux sorries**, all
else 0-sorry. **14 units fully 0-sorry** (T4 BH-dependence, T5 BH-exact, T7 conformal, T8 empirical-
Bayes; χ² exact law; KS test; e-values; goodness-of-fit). After the debt pass, the 3 remaining debts'
**main theorems are now PROVED MODULO** named cruxes (the surrounding reductions/assemblies are real):
`massart_inequality` modulo `countLE_reflection_bound` (1); `storey_fdr_le` modulo 3
(`storey_reverseMG_ost`, `storey_binom_bound`, `storey_threshold_attained`); `halfLine_isPDonsker`
(new H₀ Donsker theorem) modulo 3 framework lemmas. The 7 cruxes
are the irreducible Mathlib-absent pieces (empirical-process exponential-supermartingale, backwards-MG/
uniform-null disintegration, half-line bracketing entropy). HC's full Donoho–Jin *detection* theorem
stays honestly deferred (LIL + H₁ large deviations). NOT merged to `main` / pushed to `origin`.

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
| U-STO | `mt/storey` | `Storey` | reverse-MG,BinomialRatio | ◆ | ✅ FDR≤q assembled real, modulo 3 isolated cruxes (reverseMG-OST, binom-law, threshold-attain) — T6 |
| U-MASSART | `mt/massart` | `ForMathlib/EmpiricalProcessSup` | EMPCDF | ◆◆ | ✅ union bound + reduction real; sharp crux isolated → `countLE_reflection_bound` (1 debt) |
| U-KS | `mt/ks-test` | `GoodnessOfFit/KolmogorovSmirnov` | EMPCDF,MASSART | ● | ✅ real (merged, 0-sorry) |
| U-HC | `mt/higher-criticism` | `GoodnessOfFit/HigherCriticism` | EMPCDF,Donsker | ◆◆ | ✅ boundary+statistic+H₀ Donsker (`halfLine_isPDonsker`) real; detection theorem deferred (LIL+H₁), 3 framework debts |

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

## Residual named debts (after the debt-closing pass)
Each remaining debt is now a single, precisely-characterized named lemma with the surrounding
structure proved real (the project's planned-debt ideal).
- ✅ **χ² exact law — RETIRED** (closed by U-CHISQ-LAW via the complexMGF route).
- **Massart sharp constant** → isolated to **`countLE_reflection_bound`** (`EmpiricalProcessSup.lean`).
  `massart_inequality` is now PROVED *modulo* this one lemma: the sup-event→union-of-count-events
  reduction + `n=0` edge are real; the only gap is the `n`-fold-union→sharp-`2` collapse (Massart-1990
  exponential-supermartingale first-passage). Documented rigorously (why union-bound/McDiarmid/maximal-
  inequalities each fail; the cross-term `e^{4nuE}` blows up the McDiarmid route). Needs an
  exponential-supermartingale optional-stopping development for the empirical process. 1 debt.
- **U-HC H₀ — NOW FORMALIZED**: `halfLine_isPDonsker` (the empirical-CDF class is P-Donsker, the H₀
  empirical-process convergence) STATED + assembled from `isPDonsker_of_finite_bracketing_entropy_integral`;
  `halfLineClass_measurable` proved 0-sorry. 3 named framework debts:
  `halfLineClass_bracketingEntropyIntegral_lt_top` (the half-line entropy `N_[](ε)≲1/ε²` ⇒ integral `<∞`,
  the key one) + `halfLineClass_J_pos` + `halfLineClass_chain_bound` (generic Donsker-framework
  regularity inputs). The full Donoho–Jin **detection** theorem stays honestly deferred (residual = the
  empirical-process **LIL** `√(2 log log n)` calibration + the **H₁** sparse-mixture large deviations).
- **U-STO (`Storey.lean`)** — closing attempt `mt/storey-close` (the discrete reverse-MG via the
  uniform-null condExp) **in progress**; if it lands, the OST core is real and `storey_fdr_le` follows.
  Until then: `storey_reverseMG_ost` + `storey_fdr_le` (FDP→counting reduction already proved real).

## Book-vs-Lean constants
(populated as units land.)
