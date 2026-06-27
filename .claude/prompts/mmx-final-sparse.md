# Close #11: constant-weight Gilbert–Varshamov (SparsePacking.lean) — MOST TRACTABLE

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build). Goal 0 sorry.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/Packing/SparsePacking.lean`
Close `exists_bounded_overlap_supports (d s) (hs : 0 < s) (hsd : s ≤ d)`:
`∃ 𝒮 : Finset (Finset (Fin d)), (∀ S∈𝒮, S.card=s) ∧ (∀ S∈𝒮 S'∈𝒮, S≠S' → 2*(S∩S').card ≤ s) ∧
(s/2 : ℝ)*log((d-s)/s) ≤ log 𝒮.card`. Everything else in the file (sparseVec geometry, norm, separation,
injectivity) is PROVEN — only this combinatorial core remains. Keep signature UNCHANGED; helpers `private`.

## Strategy — Johnson-scheme GV, mirror the CLOSED `gilbert_varshamov` (HammingPacking.lean)
Read `StatLean/Minimaxity/ForMathlib/Packing/HammingPacking.lean`'s `gilbert_varshamov` proof FIRST — it is
the analogous `{0,1}^m` argument and the template. Adapt to weight-`s` supports:
1. Work inside `(Finset.univ.powersetCard s : Finset (Finset (Fin d)))` — the weight-`s` supports;
   `Finset.card_powersetCard : (univ.powersetCard s).card = (Fintype.card (Fin d)).choose s = d.choose s`.
2. Take a **maximal** `𝒮 ⊆ powersetCard s univ` with the pairwise property `2*(S∩S').card ≤ s` (extract via
   a maximum-cardinality argument over the finite `powersetCard`, like `gilbert_varshamov`). By maximality,
   every weight-`s` support `T` has some `S∈𝒮` with `2*(S∩T).card > s` (else `𝒮∪{T}` is larger).
3. So `powersetCard s univ ⊆ ⋃_{S∈𝒮} ball(S)` where `ball(S) = {T ∈ powersetCard s univ : 2*(S∩T).card > s}`.
   Hence `d.choose s ≤ 𝒮.card · max_S |ball(S)|` (`Finset.card_le_card_biUnion`-style / `card_le_sum`).
4. **Intersection-ball count**: `|ball(S)| = Σ_{j : s/2 < j ≤ s} (s.choose j)*((d-s).choose (s-j))` (choose `j`
   coords of `S` to keep, `s-j` from the complement). Bound `|ball(S)| ≤ d.choose s · ((d-s)/s)^{-s/2}`
   (the genuine combinatorial estimate — bound each term's ratio to `d.choose s`; `Nat.choose` ratio lemmas,
   `Nat.choose_le_choose`, `Nat.choose_mul_le...`). Take `log`: `log|ball| ≤ log(d.choose s) − (s/2)log((d-s)/s)`.
5. Combine 3+4: `log(d.choose s) ≤ log 𝒮.card + log|ball|` ⇒ `(s/2)log((d-s)/s) ≤ log 𝒮.card`.
For `d ≤ 2s` the RHS `(s/2)log((d-s)/s) ≤ 0` (since `(d-s)/s ≤ 1`), so a singleton `𝒮={any support}` works —
handle that branch first. Mathlib: `Finset.powersetCard`, `Finset.card_powersetCard`, `Nat.choose` bounds,
`Real.log_le_log`, `Real.log_div`, `Real.log_pow`, `Finset.card_biUnion_le`.

If the intersection-ball count `|ball(S)| ≤ d.choose s · ((d-s)/s)^{-s/2}` is the only hard step, isolate it as
ONE `private` lemma; prove the maximal-cover assembly around it. GOAL 0 sorry.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.Packing.SparsePacking` green 0 sorry. `git add` ONLY that file; commit.
