Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries.

# CONTEXT
`StatLean/HighDimensionalStatistics/ForMathlib/TopK.lean` (namespace
`StatLean.HighDimensionalStatistics`, `open Finset`, `variable {d : ℕ}`) currently has a PLACEHOLDER
`noncomputable def orderedBlocks (S) (x) (k) : ℕ → Finset (Fin d) := fun _ => ∅` and SIX interface
theorems `:= by sorry`. It imports `ForMathlib/VecNorms.lean` (`restrict`, `l1Norm`, `linfNorm`,
`l1Norm_restrict_eq_sum`, `abs_le_linfNorm`, `restrict_ofLp_apply`).

# TASK
REPLACE the placeholder `orderedBlocks` with the real greedy decreasing-magnitude partition of `Sᶜ`,
and prove all six interface lemmas to 0-sorry. Block `j` = the `j`-th consecutive window of `k`
coordinates of `Sᶜ` listed in order of DECREASING `|x.ofLp ·|` (ties broken arbitrarily, e.g. by index).

# CONSTRUCTION (recommended)
- Let `L : List (Fin d) := (Sᶜ.sort r)` where `r` is a total, antisymmetric, transitive order with
  `r a b → |x.ofLp b| ≤ |x.ofLp a|` (decreasing magnitude). Build `r` from the linear order on the
  pair `(|x.ofLp ·|, ·)` — e.g. sort by the key `fun i => (-|x.ofLp i|, (i : ℕ))` via
  `List.sort`/`Finset.sort` with a `DecidableLinearOrder`, or sort `Sᶜ.toList` with
  `List.mergeSort` and a `≤`-by-key. `Finset.sort` needs a `LinearOrder`+`IsTotal`/`IsTrans`; the
  lexicographic key gives one. Search: `./tools/loogle.sh '"Finset.sort"'`, `'"List.mergeSort"'`,
  `'"Tuple.sort"'`, `'"List.Sorted"'`, `'"List.chunk"'`, `'"List.drop"'`, `'"List.take"'`.
- `orderedBlocks S x k j := ((L.drop (j*k)).take k).toFinset`.

# INTERFACE LEMMAS TO PROVE
1. `orderedBlocks_subset_compl`: elements of the windowed list come from `L ⊆ Sᶜ` (`Finset.mem_sort`,
   `List.mem_toFinset`, `List.mem_take`/`mem_drop` ⊆ `mem`).
2. `orderedBlocks_disjoint` (`j ≠ j'`): windows `drop (j*k) |>.take k` of a **nodup** list at
   disjoint index ranges share no element (`List.Nodup` of a sorted nodup list; index-range
   disjointness). Use `List.Nodup.take`/`drop` and that the original `Sᶜ.sort` is `Nodup`.
3. `orderedBlocks_card_le`: `(l.take k).toFinset.card ≤ (l.take k).length ≤ k`
   (`List.toFinset_card_le`, `List.length_take`).
4. `mem_orderedBlocks_of_notMem` (`i ∉ S`, `0 < k`): `i ∈ Sᶜ` ⟹ `i ∈ L`; it sits at some position
   `p`; take `j = p / k`, then `i ∈ (L.drop (j*k)).take k`. (`List.mem_iff_getElem`,
   `Nat.div_mul_le_self`, `List.getElem_drop`/`getElem_take` arithmetic.)
5. `orderedBlocks_eq_empty` (`Sᶜ.card ≤ j*k`): `L.length = Sᶜ.card ≤ j*k` ⟹ `L.drop (j*k) = []`
   (`List.drop_eq_nil_of_le`, `Finset.length_sort`).
6. `linfNorm_restrict_orderedBlocks_succ_le` — THE KEY ESTIMATE. For block `B_{j+1}` and `B_j`:
   every coordinate of `B_{j+1}` has `|x.ofLp ·|` ≤ every coordinate of `B_j` (sorted decreasing ⇒
   later window entries are ≤ earlier ones). Hence `max_{i∈B_{j+1}} |x.ofLp i| ≤ min_{i∈B_j} |x.ofLp i|
   ≤ (1/|B_j|) ∑_{i∈B_j} |x.ofLp i| = (1/|B_j|) l1Norm (restrict B_j x)`. With `|B_j| = k` when `B_j`
   full (and when `B_{j+1}` is nonempty, `B_j` is full so `|B_j| = k`); if `B_{j+1} = ∅` then LHS
   `linfNorm 0 = 0 ≤ RHS`. Bridge `linfNorm (restrict B x) = max over B` and
   `l1Norm (restrict B x) = ∑_{i∈B} |x.ofLp i|` via `l1Norm_restrict_eq_sum`; min ≤ average via
   `Finset.card • (min) ≤ ∑`. Handle the empty `B_{j+1}` and the `|B_j| = k` facts from the windowing.

# REQUIREMENTS
ZERO sorry. The six lemma SIGNATURES must stay as given (downstream `RIPRecovery.lean` consumes them);
you may CHANGE the `orderedBlocks` def body (that is the point) and ADD private helper lemmas in this
file. If the construction forces a minor restatement of an interface lemma, prefer ADDING a
better-shaped lemma alongside (keep the originals provable) and note it in your report.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/ForMathlib/TopK.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.ForMathlib.TopK
# DONE = build exits 0; 0 sorries in the file; commit
  (`cs(topk): greedy decreasing-magnitude block partition + interface (Lu-BDA ch7)`).
  Report build status, sorry count, the final `orderedBlocks` definition, and any interface tweaks.
