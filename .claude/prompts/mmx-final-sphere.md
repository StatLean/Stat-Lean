# Close #10: sphere packing via the binary code embedding (SpherePacking.lean) — LOOSE CONSTANT OK

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build). Goal 0 sorry.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean`  (REWRITE to the code construction)
- `StatLean/Minimaxity/Examples/PCA.lean` — ONLY if `exists_sphere_packing`'s bound constant must change and
  PCA references it (PCA's `pca_fano_config` is a `sorry` debt, so it should still build; touch only if needed).

## NEW APPROACH — reuse the CLOSED `gilbert_varshamov` (no measure theory!)
**A loose exponential constant is explicitly acceptable.** Drop the `Measure.toSphere` / cap-fraction /
`packingNumber` route entirely (delete `two_pow_le_packingNumber_sphere` and `packingNumber_sphere_ne_top`).
Instead build the packing from the binary code:

`HammingPacking.lean` gives the CLOSED `exists_hamming_packing (m) : ∃ T : Finset (Fin m → Bool),
(m/10 : ℝ) ≤ Real.log T.card ∧ ∀ α∈T β∈T, α≠β → (m/4 : ℝ) ≤ (hammingDist α β : ℝ)`. Use it with `m = n`.

**Embedding** `Fin n → Bool  →  EuclideanSpace ℝ (Fin n)`:
`v α := WithLp.toLp 2 (fun i => (if α i then 1 else -1) / Real.sqrt n)` (entries `±1/√n`).
- `‖v α‖ = 1`: `‖v α‖² = Σ_i (1/n) = n·(1/n) = 1` (each entry squared `= 1/n`; `EuclideanSpace.norm_eq`,
  `Real.sq_sqrt`, `Finset.sum_const`).
- **Separation**: `(v α − v β) i = (2/√n)` if `α i ≠ β i` else `0`, so
  `‖v α − v β‖² = Σ_i (...)² = (hammingDist α β)·(4/n)`. With `hammingDist ≥ n/4` ⇒ `‖v α − v β‖² ≥ 1` ⇒
  `‖v α − v β‖ ≥ 1 ≥ 1/2`. (`hammingDist` counts `{i : α i ≠ β i}`; relate `(v α − v β) i ≠ 0 ↔ α i ≠ β i`.)
- **Injective** on the code (distinct codewords ⇒ `≥1`-separated ⇒ distinct images), so
  `|v '' T| = |T|`, hence `(n/10 : ℝ) ≤ Real.log |image|`.

Rewrite `sphere_packing_card` / `exists_sphere_packing` to conclude `(n/10 : ℝ) ≤ Real.log T.card` (the LOOSE
but exponential bound) with unit norms + `1/2`-separation. **Document the constant deviation** (`n·log 2 → n/10`)
in the docstring per CLAUDE.md §1 — it is still exponential, which is all the PCA Fano bound needs.

Mathlib/StatLean: `exists_hamming_packing` (HammingPacking.lean — read it), `hammingDist`,
`hammingDist_eq_card_..`/`Finset.card_filter`, `EuclideanSpace.norm_eq`, `Real.sq_sqrt`, `WithLp.toLp`,
`Finset.card_image_of_injOn`, `Real.sqrt_pos`. Mirror the structure of `SparsePacking.lean`'s `sparse_packing`
(same image-of-a-combinatorial-family pattern, already proven there).

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SpherePacking` green 0 sorry (+ PCA still builds).
`git add` the touched file(s); commit. Report the final constant + whether PCA needed a touch.
