# Close the Chapter-5 packing existence proofs: Hamming, Sphere, Sparse

Lean 4 / Mathlib proof engineer on **StatLean** (read CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster.
Run every `lake build` SYNCHRONOUSLY in the FOREGROUND (never background; never end turn mid-build).

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/Packing/HammingPacking.lean`
- `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean`
- `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean`
Keep signatures/tags/citation docstrings UNCHANGED. No axiom/admit. Helpers `private`.

These are genuine combinatorial existence results (Gilbert–Varshamov; volume/sphere packing). They are
HARD. Make an honest attempt; if a proof resists, lift its crux to a `private` lemma with ONE sorry +
`-- TODO(mmx): <which Ex 5.x fact>` and keep the file compiling. Do NOT leave the public theorem itself
as a bare sorry if you can reduce it to a single named private crux.

- `exists_hamming_packing` (Ex 5.3): a `1/4`-separated `T ⊆ {0,1}^m` with `log|T| ≥ m/10`, pairwise
  `hammingDist ≥ m/4`. Try the greedy/Gilbert–Varshamov bound: a maximal `m/4`-separated set covers
  `{0,1}^m` by Hamming balls of radius `m/4`; `|T| ≥ 2^m / vol(ball)`, and `log(vol) ≤ m·H(1/4) ≤ m·(1−1/10)`
  by the binary-entropy volume bound. Mathlib: `hammingDist`, `Finset` cardinality, `Real.binEntropy`.
- `exists_sphere_packing` (Ex 5.8): `1/2`-separated unit vectors in `ℝⁿ`, `log|T| ≥ n log 2`. Volume
  argument on the sphere. Likely a single hard crux → name it.
- `exists_sparse_packing` (Ex 5.8): `1/2`-separated `s`-sparse unit vectors, `log|T| ≥ (s/2)log((d−s)/s)`.

## DONE
`git add` ONLY the three files; commit. Report which closed fully vs which reduced to named private cruxes.
