# Close #11: sparse packing via BLOCK / q-ary Gilbert–Varshamov (SparsePacking.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build).
**DIRECTIVE: do NOT ask the user questions. Either reach 0 sorry, or leave EXACTLY ONE smaller named `private`
residual (one sorry + precise `-- TODO(mmx)`) and COMMIT. Never leave the file unchanged.**

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean`
Close `exists_bounded_overlap_supports (d s) (hs : 0 < s) (hsd : s ≤ d)`. The sparseVec geometry / norm /
separation / injectivity in the file are PROVEN — only this support-count residual remains. Loose constants OK.

## NEW route — BLOCK construction (a q-ary GV, generalizing the CLOSED binary `gilbert_varshamov`)
Read `HammingPacking.lean`'s `gilbert_varshamov` (binary, `q=2`) — generalize its maximal-code argument to `q`-ary:
1. Split `[d] = Fin d` into `s` disjoint blocks `B_0,…,B_{s-1}`, each of size `q := d/s ≥ 1` (e.g.
   `B_k = {i : k*q ≤ i.val < (k+1)*q}`; handle the remainder coords by ignoring them). A **block support** picks
   ONE coordinate from each block: `S(f) = {f 0, …, f (s-1)}` for `f : Fin s → Fin d` with `f k ∈ B_k`. Then
   `|S(f)| = s` (distinct blocks ⇒ distinct coords).
2. Two block supports `S(f), S(g)` satisfy `|S(f) ∩ S(g)| = #{k : f k = g k}` (agreement count). So
   `2|S(f)∩S(g)| ≤ s  ⟺  #{k : f k = g k} ≤ s/2  ⟺  hammingDist f g ≥ s/2` (in the `Fin s → block` alphabet).
3. **q-ary GV**: take a maximal `C ⊆ (block-choice functions)` with pairwise block-`hammingDist ≥ s/2`. By
   maximality the radius-`(s/2)` Hamming balls cover all `q^s` choice functions, so `q^s ≤ |C|·maxBall`, with
   `maxBall = Σ_{i < s/2} C(s,i)(q−1)^i`. Bound `maxBall ≤ q^{s/2}` (or `log maxBall ≤ (s/2)·log q` — a clean
   `Nat.choose`/`(q-1)^i` estimate; for `q ≥ 2`, `Σ_{i<s/2} C(s,i)(q-1)^i ≤ q^{s/2}` by comparing to the full
   `q^s = Σ C(s,i)(q-1)^i` and the tail/head split). Hence `log|C| ≥ (s/2) log q ≥ (s/2) log((d-s)/s)` (since
   `q = d/s ≥ (d-s)/s`). Map `f ↦ S(f)` (injective on `C` since distinct ⇒ disjoint-enough) to get `𝒮`.
4. `d ≤ 2s` branch: `(d-s)/s ≤ 1` ⇒ RHS `≤ 0`, a singleton `𝒮` works — do this first.
Mathlib: `Finset.image`, `hammingDist`, `Finset.card_image_of_injOn`, `Nat.choose` bounds, `Real.log_pow`,
`Real.log_le_log`, and the maximal-set extremal argument from `gilbert_varshamov`. Isolate the `maxBall ≤ q^{s/2}`
inequality as ONE `private` lemma if it is the only hard step.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SparsePacking` green (0 sorry, or 1 smaller named residual). `git add` SparsePacking.lean; COMMIT.
