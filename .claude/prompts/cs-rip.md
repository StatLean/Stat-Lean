Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE. This is a large assembly;
prove it in named pieces. 0 errors / 0 sorries at the end.

# CONTEXT
`StatLean/HighDimensionalStatistics/CompressedSensing/RIPRecovery.lean` (namespace
`StatLean.HighDimensionalStatistics`, `open Matrix`, `variable {n d : ℕ}`) has ONE theorem
`basisPursuit_recovers_of_rip` (T2) `:= by sorry`. It imports the now-PROVED
`CompressedSensing/ConeTheorem.lean` (⇒ `BasisPursuit.lean`: `unique_basisPursuit_of_cone_trivial` (A2))
and `ForMathlib/TopK.lean`. READ the merged `TopK.lean`, `BasisPursuit.lean`, `ForMathlib/VecNorms.lean`
for exact interface names. Key bricks available:
* `Defs.lean`: `IsRIP X s δ = ∀ β, IsSparse s β → (1−δ)‖β‖²≤‖designMap X β‖² ≤ (1+δ)‖β‖²`;
  `IsSparse s x = ∃ S, S.card ≤ s ∧ ∀ i∉S, x.ofLp i = 0`.
* `A2 unique_basisPursuit_of_cone_trivial : (reCone S 1 ∩ (ker (designMap X):Set _) = {0}) →
   (∀ i∉S, βstar.ofLp i = 0) → IsUniqueBasisPursuit X (designMap X βstar) βstar`.
* `TopK`: `orderedBlocks S x k : ℕ → Finset (Fin d)` with `orderedBlocks_subset_compl`,
  `orderedBlocks_disjoint`, `orderedBlocks_card_le`, `mem_orderedBlocks_of_notMem`,
  `orderedBlocks_eq_empty`, `linfNorm_restrict_orderedBlocks_succ_le`
  (`‖x|_{B_{j+1}}‖∞ ≤ (1/k)‖x|_{B_j}‖₁`).
* `VecNorms`: `l1Norm_split`, `restrict_add_restrict_compl`, `norm_le_sqrt_card_mul_linfNorm`
  (`‖x|_S‖ ≤ √|S|·‖x|_S‖∞`), `norm_restrict_le_of_subset`, `l1Norm_restrict_le_sqrt_card_mul_norm`
  (`‖x|_S‖₁ ≤ √|S|·‖x‖`), `l1Norm_restrict_eq_sum`, `l1Norm_add_le`.

# STRATEGY
Prove the private **null-space-property core** and finish via A2:
```
rip_cone_trivial : (S.card ≤ s) → IsRIP X (3*s) δ → 0 < δ → δ < 1/3 →
   reCone S 1 ∩ (ker (designMap X) : Set _) = {0}
```
Then `basisPursuit_recovers_of_rip`: from `hsp : IsSparse s βstar` obtain `S` with `S.card ≤ s` and
`hsupp : ∀ i∉S, βstar.ofLp i = 0`; apply `unique_basisPursuit_of_cone_trivial X S (rip_cone_trivial …) βstar hsupp`.

## Proof of `rip_cone_trivial` (book `thm:rip`)
`{0} ⊆ …` is trivial. For `… ⊆ {0}`: take `Δ` with `Δ ∈ reCone S 1`
(`l1Norm (restrict Sᶜ Δ) ≤ l1Norm (restrict S Δ)`) and `designMap X Δ = 0`; show `Δ = 0`.
Handle `s = 0` first: then `S = ∅`, `restrict S Δ = 0`, the cone forces `l1Norm (restrict Sᶜ Δ) ≤ 0`,
so `restrict Sᶜ Δ = 0`, and `Δ = restrict S Δ + restrict Sᶜ Δ = 0`. Assume `0 < s` below.
Let `k = 2*s`, `B j = orderedBlocks S Δ k j`, `T₀ = S ∪ B 0`.
1. **Block ℓ²→ℓ¹ shift.** For `j ≥ 0`: `‖restrict (B (j+1)) Δ‖ ≤ √k · ‖restrict (B (j+1)) Δ‖∞
   ≤ √k · (1/k)·l1Norm (restrict (B j) Δ) = (1/√k)·l1Norm (restrict (B j) Δ)`
   (`norm_le_sqrt_card_mul_linfNorm` + `linfNorm_restrict_orderedBlocks_succ_le`; `√k·(1/k)=1/√k`).
2. **RIP on the head vs tail.** `designMap X Δ = 0` and `Δ = restrict T₀ Δ + ∑_{j≥1} restrict (B j) Δ`
   (the blocks + `S` partition the coordinates — use `restrict_add_restrict_compl`, the block partition,
   and `orderedBlocks_eq_empty` so the sum is a finite `Finset.range N`, `N` with `Sᶜ.card ≤ N*k`).
   So `designMap X (restrict T₀ Δ) = − ∑_{j≥1} designMap X (restrict (B j) Δ)`. `restrict T₀ Δ` is
   `3s`-sparse (`T₀.card ≤ s + 2s = 3s`) and each `restrict (B j) Δ` is `≤ 2s ≤ 3s`-sparse, so RIP gives
   `√(1−δ)·‖restrict T₀ Δ‖ ≤ ‖designMap X (restrict T₀ Δ)‖ ≤ ∑_{j≥1} ‖designMap X (restrict (B j) Δ)‖
     ≤ √(1+δ)·∑_{j≥1} ‖restrict (B j) Δ‖`  (triangle `norm_sum_le`, RIP lower on head, RIP upper on tail).
   To use `IsRIP`, supply each restriction's `IsSparse (3*s)` witness (the support finset has card ≤ 3s).
3. **Collapse the tail sum.** `∑_{j≥1} ‖restrict (B j) Δ‖ ≤ (1/√k) ∑_{j≥0} l1Norm (restrict (B j) Δ)
     = (1/√k)·l1Norm (restrict Sᶜ Δ)` (step 1 termwise + blocks partition `Sᶜ`, so
   `∑_j l1Norm (restrict (B j) Δ) = l1Norm (restrict Sᶜ Δ)` via `l1Norm_restrict_eq_sum` +
   `Finset.sum_biUnion`/disjoint partition).
4. **Lower bound the head.** `‖restrict T₀ Δ‖ ≥ ‖restrict S Δ‖ ≥ (1/√s)·l1Norm (restrict S Δ)`
   (`norm_restrict_le_of_subset (S ⊆ T₀)`, and `l1Norm_restrict_le_sqrt_card_mul_norm` rearranged with
   `S.card ≤ s`).
5. **Contraction.** Combine 2–4: `√(1−δ)·(1/√s)·l1Norm (restrict S Δ) ≤ √(1+δ)·(1/√k)·l1Norm (restrict Sᶜ Δ)`.
   With `k = 2s`, `√s/√k = 1/√2`, so `l1Norm (restrict S Δ) ≤ √((1+δ)/(2(1−δ)))·l1Norm (restrict Sᶜ Δ)`.
   Set `ρ = √((1+δ)/(2(1−δ)))`; `ρ < 1 ⟺ (1+δ) < 2(1−δ) ⟺ 3δ < 1 ⟺ δ < 1/3` (`Real.sqrt_lt_one`,
   `nlinarith`). With the cone `l1Norm (restrict Sᶜ Δ) ≤ l1Norm (restrict S Δ)`:
   `l1Norm (restrict S Δ) ≤ ρ·l1Norm (restrict S Δ)` ⟹ `l1Norm (restrict S Δ) = 0` (ρ<1, nonneg) ⟹
   `l1Norm (restrict Sᶜ Δ) = 0`. Both restrictions have 0 ℓ¹ norm ⟹ are 0 ⟹ `Δ = 0`.

# REQUIREMENTS
ZERO sorry. Keep T2's name/signature/tags. You may add private lemmas in THIS file only. The book's
`δ < 1/3` is exact — keep it. If a block index/`√(2s)` step needs `s > 0`, branch on `s = 0` as above.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/CompressedSensing/RIPRecovery.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.CompressedSensing.RIPRecovery
# DONE = build exits 0; 0 sorries; commit (`cs(rip): perfect recovery under RIP T2 (Lu-BDA ch7, thm:rip)`).
  Report build status, sorry count, named pieces, any step that needed adjustment.
