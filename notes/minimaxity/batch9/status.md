# Batch 9 — Minimaxity: status ledger

**Branch** `mmx/batch9` (off `main`). **Pin** v4.29.1. **Reference** Wainwright Ch. 15.
Source of truth = `lake build` sorry inventory; this doc tracks intent/progress.

## State

**Wave 0 (stubbing) — core complete.** Umbrella `StatLean.Minimaxity` stub-gates **green** (0 errors,
32 sorries). **22/29 files** drafted and cluster-green (the plan's 30 minus the `FanoInequality`
merge into `FanoLowerBound`). The entire core theory — keystone risk encoding, all Le Cam / Fano /
local-packing / Yang–Barron method theorems, the three divergences + Pinsker + Le Cam inequality, the
entropy appendix, Gaussian KL + max-entropy, three Chapter-5 packing bricks, and the two parametric
examples — is stated, cited, and type-checking.

**Remaining stubs (7), all hard nonparametric / custom-construction — draft with focused design,
do NOT hypothesis-launder:** `ForMathlib/Packing/SobolevEntropy` (Ex 5.12, ◆◆ infinite-dim ellipsoid)
and the 6 examples `Examples/{LinearRegression (prediction semimetric via Ω = pred-space),
PCA (spiked covariance), LipschitzDensity, QuadraticFunctional, DensityEstimation, Sobolev}`.

**Then:** proof closure — fan out the 32 `sorry`s 4+ concurrent via `lean-fasrc-cluster-claude`,
verify each (fresh build + `#print axioms` + diff ⊆ touch-set + six-check), merge to `main`.

## Unit ledger

Diff: ● moderate · ◆ hard · ◆◆ research-grade. Stub: ✅ green · ⏳ gating · ▢ todo.

| # | Unit (file) | Book | Stub | Proof | Diff |
|---|---|---|---|---|---|
| C0 | `Defs` (laptop) | §15.1 | ✅ 0-sorry | n/a | — |
| F1 | `ForMathlib/KLDivergence` | 15.11, Ex 15.11 | ✅ | ▢ | ● |
| F2 | `ForMathlib/TotalVariation` | 15.5/15.6, Ex 15.1 | ✅ | ▢ | ● |
| F3 | `ForMathlib/HellingerDivergence` | 15.9, 15.12 | ✅ | ▢ | ● |
| F4 | `ForMathlib/PinskerInequality` | Lemma 15.2 | ✅ | ▢ | ◆ |
| F5 | `ForMathlib/LeCamInequality` | Lemma 15.3 | ✅ | ▢ | ◆ |
| F6 | `ForMathlib/GaussianKL` | Ex 15.13 | ⏳ | ▢ | ◆ |
| F7 | `ForMathlib/Entropy` | Def 15.24/25, 15.60 | ▢ | ▢ | ◆ |
| F8 | `ForMathlib/GaussianMaxEntropy` | Lemma 15.17 | ▢ | ▢ | ◆◆ |
| P1 | `ForMathlib/Packing/HammingPacking` | Ex 5.3 | ✅ | ▢ | ◆ |
| P2 | `ForMathlib/Packing/SpherePacking` | Ex 5.8 | ✅ | ▢ | ◆ |
| P3 | `ForMathlib/Packing/SparsePacking` | Ex 5.8 | ✅ | ▢ | ◆ |
| P4 | `ForMathlib/Packing/SobolevEntropy` | Ex 5.12 | ▢ | ▢ | ◆◆ |
| A1 | `EstimationToTesting` | Prop 15.1 | ✅ | ▢ | ● |
| L1 | `LeCam/TwoPoint` | 15.13/14 | ✅ | ▢ | ● |
| L2 | `LeCam/ConvexHull` | Lemma 15.9 | ▢ | ▢ | ◆ |
| L3 | `LeCam/Functional` | 15.17, Cor 15.6 | ▢ | ▢ | ◆ |
| N1 | `Fano/MutualInformation` | 15.29/30/34 | ✅ | ▢ | ● |
| N2 | `Fano/FanoLowerBound` | 15.31, Prop 15.12 | ✅ | ▢ | ● |
| N3 | `Fano/LocalPacking` | 15.35 | ⏳ | ▢ | ◆ |
| N4 | `Fano/YangBarron` | Lemma 15.21 | ⏳ | ▢ | ◆ |
| E1–E8 | `Examples/{GaussianLocation,UniformLocation,LipschitzDensity,QuadraticFunctional,LinearRegression,DensityEstimation,PCA,Sobolev}` | Ex 15.4–15.23 | ▢ | ▢ | ◆/◆◆ |

## Risk items (time-boxed; escalate, do not silently sorry)

- **F8 GaussianMaxEntropy** (Lemma 15.17) — needs multivariate-Gaussian max-entropy + log-det concavity.
- **P4 SobolevEntropy** (Ex 5.12) — Kolmogorov–Tikhomirov metric entropy `(1/δ)^{1/α}`.
- **N2 fano_inequality** — proof needs the entropy machinery (F7) for Eq. (15.61).

## Book-vs-Lean constants

To be reconciled as proofs land. Expected: Le Cam two-point `Φ(δ)/2` (15.14); Fano `(I+log2)/log M`
(15.31); local packing `½Φ(δ)` (15.35); Pinsker `√(½ KL)`; example pre-factors (σ²/24n etc.) stated
as provable — deviations documented in declaration docstrings.

## Lessons

- Measurable-space binders **must be instance-implicit** `[…]` in files using `minimaxRiskDist`
  (Ω's measurable space is otherwise an unsynthesizable regular implicit — not pinned by `g : Θ → Ω`).
- Full-citation docstrings push past the 100-col lint — wrap the `Chapter … / Eq. … -/` line.
- Mathlib reuse confirmed: `ProbabilityTheory.{minimaxRisk,bayesRisk}` + DPI; `klDiv` arg order =
  Wainwright `D(Q‖P)`; `StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct`.
