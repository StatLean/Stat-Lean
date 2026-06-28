# Close (or honestly named-debt) GaussianMaxEntropy (Lemma 15.17) + SobolevEntropy (Ex 5.12)

Lean 4 / Mathlib proof engineer on **StatLean** (read CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster.
Run every `lake build` SYNCHRONOUSLY in the FOREGROUND (never background; never end turn mid-build).

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/GaussianMaxEntropy.lean`  (Lemma 15.17, log-det MI bound)
- `StatLean/Minimaxity/ForMathlib/Packing/SobolevEntropy.lean`  (Ex 5.12, ellipsoid metric entropy)
Keep signatures/tags/citation docstrings UNCHANGED. No axiom/admit.

These are research-grade (◆◆). If you cannot fully close, REDUCE each public theorem to a single named
`private` lemma carrying one `sorry` + `-- TODO(mmx): <precise missing fact>`, so the public theorem is
NOT a bare sorry and the file compiles. For `gaussian_mutualInfo_le`, the structural steps (mutual-info =
KL of joint vs product; log-det concavity / Jensen) may be partially dischargeable — do what you honestly
can, name the residual. For `sobolev_packing_lower_bound`, the Kolmogorov–Tikhomirov entropy is almost
certainly a single named debt — isolate it cleanly.

## DONE
`git add` ONLY the two touch-set files; commit `mmx(batch9): close mmx/p-gauss-sobolev`. Report what
closed vs named-debt with the precise residual.
