# Close #11: sparse packing via block/q-ary GV (SparsePacking.lean) — LOOSE CONSTANT (weaken the bound)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build).
**DIRECTIVE: do NOT ask questions. The exact constant is unreachable by GV — WEAKEN it (loose constant is APPROVED). Reach 0 sorry or leave ONE smaller named residual + COMMIT.**

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean` (close `exists_bounded_overlap_supports_gv`, ≈line 139)
- `StatLean/Minimaxity/Examples/LinearRegression.lean` — ONLY if it references the exact bound constant (it is a
  `sorry` debt; should still build). Adjust if needed.
The sparseVec geometry / norm / separation / injectivity + the `d≤2s` branch (in `exists_bounded_overlap_supports`)
are PROVEN. Helpers `private`.

## The exact constant is UNREACHABLE — weaken it
The current goal `(s/2)·log((d−s)/s) ≤ log|𝒮|` for `2s<d` is NOT achievable by Gilbert–Varshamov (the file's
TODO: sharp constant-weight GV gives `~135 < 243` for `d=40,s=10`; the exact constant needs Reed–Solomon codes).
**WEAKEN** the conclusion of `exists_bounded_overlap_supports_gv` (and propagate through `sparse_packing` /
`exists_sparse_packing`) to a provable looser EXPONENTIAL bound such as
`(s/2)·Real.log (d/s) − s·Real.log 2 − Real.log s ≤ log|𝒮|`  (or `c·s·Real.log((d−s)/s) − c'·s` for explicit
`c,c'>0`). Document the deviation in the docstring per CLAUDE.md §1. Keep the unit-norm + `1/2`-separation +
support-card parts of `exists_sparse_packing` UNCHANGED.

## Strategy — block / q-ary GV (mirror the CLOSED binary `gilbert_varshamov`)
READ `StatLean/Minimaxity/ForMathlib/Packing/HammingPacking.lean` `gilbert_varshamov` — the binary template.
1. `q := d / s` (≥ 2 since `2s < d`). Partition `Fin d` into `s` blocks `B_k` of size `q` (e.g. `B_k = {i :
   k*q ≤ i.val < (k+1)*q}`; ignore the `d − s*q` leftover coords). A **block support** = one coord per block ↔
   `f : Fin s → Fin q`, `S(f) = {blockCoord k (f k) : k}`, `|S(f)| = s`.
2. `2|S(f)∩S(g)| ≤ s ⟺ #{k : f k = g k} ≤ s/2 ⟺ hammingDist f g ≥ s/2` (`hammingDist` on `Fin s → Fin q`).
3. **q-ary GV**: take a maximal `C ⊆ (Fin s → Fin q)` with pairwise `hammingDist ≥ s/2` (maximal-set extraction
   exactly as in `gilbert_varshamov`). Maximality ⇒ radius-`(s/2)` balls cover all `q^s` functions ⇒
   `q^s ≤ |C| · ballVol`, `ballVol = #{g : hammingDist f g < s/2} = Σ_{i<s/2} C(s,i)(q−1)ⁱ`.
4. **Crude ball bound** (elementary — avoids the sharp entropy estimate): `ballVol ≤ s · C(s,⌊s/2⌋)·(q−1)^{s/2}
   ≤ s · 2^s · q^{s/2}` (≤ `s` terms; each `C(s,i)(q−1)ⁱ ≤ C(s,⌊s/2⌋)(q−1)^{s/2}` for `i<s/2`, `q≥2`; and
   `C(s,⌊s/2⌋) ≤ 2^s` by `Nat.choose_le_two_pow`/`Nat.choose_le_middle`). Hence
   `log|C| ≥ s·log q − log(ballVol) ≥ (s/2)·log q − s·log 2 − log s`. (`Commute.add_pow` gives
   `q^s = Σ C(s,i)(q−1)ⁱ` if you prefer; `Real.log_pow`, `Real.log_mul`, `Real.log_le_log`.)
5. Map `f ↦ S(f)` (injective: distinct `f` ⇒ `hammingDist ≥ s/2 > 0` ⇒ distinct supports) → `𝒮 = C.image S`,
   `|𝒮| = |C|`, and transport the separation `2|S∩S'| ≤ s`.

Counting / log-rearrangement / maximal-set scaffolding from `gilbert_varshamov` is alphabet-agnostic — reuse it.
If only the ball bound resists, isolate `q_ary_ball_card_le` as ONE `private` lemma.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SparsePacking` green (+ LinearRegression builds). `git add` touched files; COMMIT. Report the final weakened constant.
