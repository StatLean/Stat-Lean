# Close #11: sparse-vector packing (SparsePacking.lean) — depends on #10

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean`
Close `sparse_packing (d s) (hs : 0 < s) (hsd : s ≤ d) : ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
(s/2)·log((d−s)/s) ≤ log T.card ∧ (∀ v∈T, ‖v‖=1 ∧ support-card ≤ s) ∧ pairwise 1/2-separated`.
Keep signature UNCHANGED; helpers `private`.

## Available (proven, black-box)
- `ForMathlib/Packing/SpherePacking.lean`: `sphere_packing_card` (≥2^s separated unit vectors in ℝ^s) /
  `exists_sphere_packing` (now CLOSED in #10).
- `ForMathlib/Packing/HammingPacking.lean`: `gilbert_varshamov` / `exists_hamming_packing` (CLOSED) — a
  `m/4`-separated `T ⊆ {0,1}^m` with `log|T| ≥ m/10`.

## Strategy
Combine support-selection with per-support sphere packing. Fix the support pattern via a Hamming packing of
`{0,1}^d` restricted to weight-`s` supports (or use `gilbert_varshamov`), and on each chosen `s`-subset embed
`sphere_packing_card s` (the `s`-dim unit-sphere packing) into the corresponding coordinates of `ℝ^d`. Distinct
supports give vectors that differ in ≥ (separation) coordinates; same-support vectors inherit the sphere
`1/2`-separation. Count: `log|T| ≥ (s/2)·log((d−s)/s)` from the `C(d,s)` support count + per-support `2^s`.
Mathlib: `Finset.powersetCard`, `Nat.choose`, `EuclideanSpace` coordinate embedding, `‖·‖` on supported vectors.
You MAY tune constants to make a clean bound provable — document deviations in the docstring. Isolate the
support-counting core as ONE `private` lemma if needed.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SparsePacking` green (0 sorry or ≤1 named residual).
`git add` ONLY that file; commit.
