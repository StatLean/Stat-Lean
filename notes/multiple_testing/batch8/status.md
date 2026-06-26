# Batch 8 — Candès STAT 300C — status

**STATE:** Wave 0 in progress. Integration branch `mt/batch8` (off `main` @ `f043f2a`).
Reference: Candès STAT 300C lecture notes. See `outline.md` for targets, DAG, reuse, constants.

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
| U-EV | `mt/evalues` | `EValues/{Defs,Conversion}` | PValues | ◐ | Defs bug fixed (lintegral); re-closing |
| U-GAUSS | `mt/gauss-moments` | `ForMathlib/GaussianMoments` | — | ● | todo |
| U-GAMMA | `mt/gamma-moments` | `ForMathlib/GammaMoments` | — | ● | todo |
| U-EMPCDF | `mt/empirical-cdf` | `ForMathlib/EmpiricalCDF` | — | ● | stub written |
| U-RANK | `mt/rank-uniform` | `ForMathlib/RankUniform` | — | ● | todo |
| U-BHD | `mt/bh-dependent` | `BHDependence` | FDP,PValues,harmonic | ◆ | todo |
| U-CHISQ | `mt/chisquared-dist` | `ForMathlib/ChiSquared` | GAUSS,GAMMA | ◆ | todo |
| U-EB | `mt/empirical-bayes` | `EmpiricalBayes/{Defs,BayesRisk}` | GAUSS | ● | todo |
| U-CONF | `mt/conformal` | `Conformal/{Defs,Coverage}` | RANK | ● | todo |
| U-REVMG | `mt/reverse-martingale` | `ForMathlib/ReverseMartingale` | EMPCDF,OptStop | ◆ | todo |
| U-BHM | `mt/bh-martingale` | `BHMartingale` | EMPCDF,REVMG | ◆ | todo |
| U-STO | `mt/storey` | `Storey` | REVMG,BinomialRatio | ● | todo |
| U-MASSART | `mt/massart` | `ForMathlib/EmpiricalProcessSup` | EMPCDF | ◆◆ | todo |
| U-KS | `mt/ks-test` | `GoodnessOfFit/KolmogorovSmirnov` | EMPCDF,MASSART | ● | todo |
| U-HC | `mt/higher-criticism` | `GoodnessOfFit/HigherCriticism` + `ForMathlib/BrownianBridgeLIL` | MASSART | ◆◆ | todo |

Concept `Defs.lean` (laptop-only, no sorry): `EValues/Defs` ✓ written;
`ChiSquaredTest/Defs`, `GoodnessOfFit/Defs`, `EmpiricalBayes/Defs`, `Conformal/Defs` — todo.

## Waves (dependency-respecting, ≤3 concurrent)

- Wave 0: Defs + stubs + prompts + umbrella; stub-gate green-with-sorries. **← here**
- A1: GAUSS · GAMMA · EMPCDF   A2: EV · RANK · BHD
- B1: CHISQ · EB · CONF   B2: CHI · REVMG   B3: BHM · STO
- C1: MASSART   C2: KS · HC

## Vertical-slice de-risk (current)

U-EV taken end-to-end first (Defs + assembly stub + umbrella + prompt) to validate the pipeline
(conventions compile, cluster stub-gate, worktree mechanics) before mass-producing the rest.

## Lessons / gotchas
- **Bochner `∫ f ∂μ ≤ C` is unsound for "expectation ≤ C" predicates.** Mathlib's Bochner integral
  of a *non-integrable* function is `0` (`integral_undef`), so a nonneg non-integrable `f` satisfies
  `∫ f ≤ C` vacuously with infinite true expectation. Use the **lintegral** `∫⁻ ofReal(f) ∂μ ≤ C`
  (genuine expectation for nonneg `f`; bound forces finiteness ⇒ integrability). Caught by the
  cluster gate on U-EV — `IsEVariable.expectation_le_one` switched Bochner→lintegral; both
  conversion theorems were false under the Bochner form (counterexample `E ω = 2/ω` on `(0,1)`).

## Residual named debts
(none yet — populated as units land; U-MASSART sharp-constant and U-HC Donsker/LIL are the
anticipated documented-`sorry` debts.)

## Book-vs-Lean constants
(populated as units land.)
