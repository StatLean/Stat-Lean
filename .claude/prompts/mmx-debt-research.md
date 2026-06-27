# Attempt the two research-grade debts: Gaussian max-entropy (15.17) + Sobolev entropy (5.12)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.
These need theory absent from Mathlib AND StatLean (differential entropy of measures; metric entropy of
smoothness classes). Your job: build as much real infrastructure as you honestly can and SHRINK each debt to
the smallest possible named `private` core; do not fake it.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/GaussianMaxEntropy.lean` (`sum_klDiv_le_logdet`)
- `StatLean/Minimaxity/ForMathlib/Packing/SobolevEntropy.lean` (`sobolev_packing_lower_bound`)
Keep public signatures/docstrings UNCHANGED. Helpers `private`.

## `sum_klDiv_le_logdet` (Lemma 15.17): `(1/M)Σ klDiv(𝒩(0,Σʲ)) (mixture) ≤ ½(log det covZ − (1/M)Σ log det Σʲ)`
Plan: (a) define differential entropy `private noncomputable def diffEntropy (μ) := -∫ x, Real.log (μ.rnDeriv volume x).toReal ∂μ`;
(b) prove `diffEntropy (multivariateGaussian 0 Σ) = ½ log((2πe)^d det Σ)` (Gaussian density log-integral — use
`multivariateGaussian` density, `Matrix.det`, Gaussian moment integrals); (c) the identity
`I(Z;J) = diffEntropy(mixture) − (1/M)Σ diffEntropy(𝒩(0,Σʲ))`; (d) Gaussian MAX-ENTROPY: `diffEntropy(mixture)
≤ ½ log((2πe)^d det covZ)` (the mixture has covariance covZ; Gaussian maximizes entropy at fixed covariance —
this is the deep step, may need `≤` via a relative-entropy-to-Gaussian ≥ 0 argument). The `(2πe)^d` cancels.
If the max-entropy step (d) is the irreducible gap, isolate it as ONE named `private gaussian_max_entropy`
(single sorry + `-- TODO(mmx): Gaussian maximizes differential entropy at fixed covariance, Ex 15.14`) and
PROVE (a),(b),(c) and the assembly around it.

## `sobolev_packing_lower_bound` (Ex 5.12): `∃ δ-separated T ⊆ ℓ²-ellipsoid, log|T| ≳ (1/δ)^{1/α}`
Kolmogorov–Tikhomirov: truncate the ellipsoid to its first `k ≍ (1/δ)^{1/α}` coordinates (a `k`-dim box of
side `≍ δ`), then run a Gilbert–Varshamov / volume packing of that box. If the full K–T bound is irreducible,
isolate the box-packing core as ONE named `private` lemma (single sorry + precise `-- TODO(mmx)`) and prove the
ellipsoid-membership / truncation / lp-embedding scaffolding around it.

GOAL: shrink each debt maximally; honest named residual for the genuine infrastructure gap.
## DONE: build both modules green; `git add` only the two files; commit. Report exactly what infra you built
and the precise residual that remains (if any).
