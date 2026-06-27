# Close the worked example minimax-rate theorems (Wainwright §15.2–15.3)

Lean 4 / Mathlib proof engineer on **StatLean** (read CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster.
Run every `lake build` SYNCHRONOUSLY in the FOREGROUND (never background; never end turn mid-build).

## Touch-set (edit ONLY these example files)
- `StatLean/Minimaxity/Examples/GaussianLocation.lean`  (Ex 15.4: rate v/(24n))
- `StatLean/Minimaxity/Examples/UniformLocation.lean`    (Ex 15.5: rate n^-2)
- `StatLean/Minimaxity/Examples/LinearRegression.lean`   (Ex 15.14: v·rank/(128n))
- `StatLean/Minimaxity/Examples/PCA.lean`                (Ex 15.19)
- `StatLean/Minimaxity/Examples/LipschitzDensity.lean`   (Ex 15.7/15.8)
- `StatLean/Minimaxity/Examples/QuadraticFunctional.lean`(Ex 15.11)
- `StatLean/Minimaxity/Examples/DensityEstimation.lean`  (Ex 15.15)
- `StatLean/Minimaxity/Examples/Sobolev.lean`            (Ex 15.23)
Keep signatures/tags/citation docstrings UNCHANGED. No axiom/admit. Helpers `private`.

Each example APPLIES an already-proven method theorem (use as black box, even if itself `sorry`):
`minimax_two_point`, `minimax_le_cam_convex_hull`, `minimax_functional_modulus`,
`minimax_fano_lower_bound`, `minimax_local_packing`. Strategy per example: instantiate the method
theorem with the example's family + the supplied hypotheses (`hP`/`hsep`/`h35a`/`h35b`), then discharge
the arithmetic that the supplied separation/KL bounds imply the stated rate (ℝ≥0∞ `ofReal` monotonicity,
`gcongr`, `nlinarith`). For `DensityEstimation`/`Sobolev` the hypotheses already encode the local
packing — the proof is mostly plugging into `minimax_local_packing` and simplifying `δ²`.

If an example's arithmetic resists, lift the crux to a `private` lemma (one sorry + `-- TODO(mmx)`).
Work file-by-file; commit after EACH file builds (so partial progress is saved):
`git add <that one file> && git commit -m 'mmx(batch9): close <file> example'`.

## DONE
Report per example: closed fully vs named-debt, and the method theorem used.
