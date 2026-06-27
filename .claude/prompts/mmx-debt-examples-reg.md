# Close regression/PCA example Fano-config debts

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/Examples/LinearRegression.lean` (`linreg_local_packing_data`)
- `StatLean/Minimaxity/Examples/PCA.lean` (`pca_fano_config`)
Keep public signatures/docstrings UNCHANGED. Helpers `private`. Black-box `exists_sphere_packing`,
`exists_sparse_packing` (packing — may be proven in parallel), `klDiv_gaussianReal`,
`gaussian_mutualInfo_le` (Lemma 15.17 — may be a debt; use as black box).

## `linreg_local_packing_data` (Ex 15.14): build the 2δ-separated family for `minimax_local_packing`
From `exists_sphere_packing`/`exists_sparse_packing` get a `δ√n`-packing `{θʲ}` in the prediction norm with
`log M ≥ r·log 2` (`r = rank`); the design map `A` carries it. Pairwise KL `D(P_{θʲ}‖P_{θᵏ}) =
‖A(θʲ−θᵏ)‖²/(2v)` (Gaussian, via `klDiv_gaussianReal` multivariate / `multivariateGaussian` KL) ≤ `c²nδ²`
(15.35a), and `log M ≥ 2(c²nδ²+log2)` (15.35b) for the chosen `δ² = v·r/(64n)`. Assemble the `∃ M θfam … `
witness. Mathlib: `Matrix`, `Module.finrank`, `multivariateGaussian` KL.

## `pca_fano_config` (Ex 15.19): spiked-covariance Fano configuration
From `exists_sphere_packing` (½-packing of `𝕊^{d−1}`, `log M ≥ d/2`) build the `θⱼ`; the mutual information
`I(Z;J) ≤ ½ log M` follows from `gaussian_mutualInfo_le` (Lemma 15.17, log-det bound on the spiked
covariances `I + ν θⱼθⱼᵀ`), so Fano's `(1 − (I+log2)/log M) ≥ ½`, giving `δ² ≍ min{(1+ν)/ν²·d/n,1}`.
NOTE: this depends on `gaussian_mutualInfo_le` which is itself research-grade — if it's still a debt, this
config will transitively depend on it; close everything else and isolate the residual cleanly.

GOAL: close each; reduce residuals to SMALLER named `private` sorries + precise `-- TODO(mmx)`.
## DONE: build both modules green; `git add` only the two files; commit. Report closed/residual + lemmas.
