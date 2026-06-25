Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries.

# CONTEXT
`StatLean/HighDimensionalStatistics/CompressedSensing/ConeTheorem.lean` (namespace
`StatLean.HighDimensionalStatistics`, `open Matrix`, `variable {n d : ℕ}`) has TWO theorems
`:= by sorry`: `cone_trivial_of_unique_basisPursuit` (A3, necessity) and
`basisPursuit_unique_iff_cone_inter_ker` (T1, the cone theorem). It imports
`CompressedSensing/BasisPursuit.lean`, which is NOW PROVED (0-sorry) and exposes:
* `deviation_mem_cone_of_basisPursuit` (A1),
* `unique_basisPursuit_of_cone_trivial` (A2) :
   `(reCone S 1 ∩ (ker (designMap X) : Set _) = {0}) → (∀ i∉S, βstar.ofLp i = 0)
      → IsUniqueBasisPursuit X (designMap X βstar) βstar`.
Read the MERGED `BasisPursuit.lean` and `ForMathlib/VecNorms.lean` for the exact names of the helper
lemmas they expose (e.g. `restrict_add_restrict_compl`, `l1Norm_split`, `restrict_ofLp_apply`,
and possibly `l1Norm_neg`/`restrict_add`). The cone is `reCone S 1` (`Lasso/Defs.lean`).

# TASK — close both sorries to 0-sorry.

## T1 `basisPursuit_unique_iff_cone_inter_ker`
This is `Iff.intro`:
* `mp` is exactly `cone_trivial_of_unique_basisPursuit X S` (A3 below).
* `mpr` is `fun htriv βstar hsupp => unique_basisPursuit_of_cone_trivial X S htriv βstar hsupp` (A2).
So T1 is a one-liner once A3 is done.

## A3 `cone_trivial_of_unique_basisPursuit` (book `thm:cone` ⟹, contrapositive)
Prove set equality `reCone S 1 ∩ (ker (designMap X) : Set _) = {0}` by `Set.eq_singleton_iff...`/
`subset_antisymm`:
* `{0} ⊆ …`: `0 ∈ reCone S 1` (both `l1Norm` sides are 0) and `0 ∈ ker`.
* `… ⊆ {0}`: take `v` with `v ∈ reCone S 1` (`l1Norm (restrict Sᶜ v) ≤ 1 * l1Norm (restrict S v)`) and
  `designMap X v = 0`. Set `βstar := restrict S v` (supported on `S`: `restrict_ofLp_apply` gives 0 off
  `S`) and the competitor `β := - restrict Sᶜ v`. Then:
  - feasibility `designMap X β = designMap X βstar`: from `restrict_add_restrict_compl S v`
    (`restrict S v + restrict Sᶜ v = v`) and `designMap X v = 0` (`map_add`/`map_neg`):
    `designMap X (restrict S v) = - designMap X (restrict Sᶜ v)`.
  - `l1Norm β = l1Norm (restrict Sᶜ v) ≤ l1Norm (restrict S v) = l1Norm βstar`
    (use `l1Norm` of a negation = `l1Norm` — prove a private `l1Norm_neg` in THIS file if VecNorms
    doesn't expose it; and `one_mul` for the cone).
  - Apply the uniqueness clause of `(h βstar hsupp : IsUniqueBasisPursuit …).2` to `β`: get `β = βstar`,
    i.e. `- restrict Sᶜ v = restrict S v`. Since `restrict S v` is supported on `S` and `restrict Sᶜ v`
    on `Sᶜ` (disjoint), this forces `restrict S v = 0` and `restrict Sᶜ v = 0` (compare coordinates with
    `restrict_ofLp_apply`, `Finset.mem_compl`), hence `v = restrict S v + restrict Sᶜ v = 0`.

# REQUIREMENTS
ZERO sorry. Keep theorem names/signatures/tags. You may add private helper lemmas in THIS file only.
Consume A1/A2 and the VecNorms bricks from the already-merged files; do not edit them.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/CompressedSensing/ConeTheorem.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.CompressedSensing.ConeTheorem
# DONE = build exits 0; 0 sorries; commit (`cs(cone): the cone theorem T1 (Lu-BDA ch6, thm:cone)`).
  Report build status, sorry count, helper lemmas added.
