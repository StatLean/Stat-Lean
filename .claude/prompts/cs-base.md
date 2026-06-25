Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries.

# CONTEXT (read carefully; do NOT modify other files)
`StatLean/HighDimensionalStatistics/ForMathlib/VecNorms.lean` already defines, in namespace
`StatLean.HighDimensionalStatistics` (`open scoped InnerProductSpace`, `open Finset`, `variable {d : ℕ}`):
* `l1Norm x = ∑ i, |x.ofLp i|`, `linfNorm x = ⨆ i, |x.ofLp i|`,
* `restrict S x = WithLp.toLp 2 (fun i => if i ∈ S then x.ofLp i else 0)`,
* `@[simp] restrict_ofLp_apply : (restrict S x).ofLp i = if i ∈ S then x.ofLp i else 0`,
* `l1Norm_restrict_eq_sum : l1Norm (restrict S x) = ∑ i ∈ S, |x.ofLp i|`,
* `abs_le_linfNorm : |x.ofLp i| ≤ linfNorm x`, `norm_restrict_le_norm`,
* `l1Norm_restrict_le_sqrt_card_mul_norm` (a √card bound — a good STYLE TEMPLATE for the ℓ²–ℓ∞ lemma).
At the bottom of that file there are FIVE new lemmas currently `:= by sorry` (find them under
"Additional bricks for compressed sensing"): `l1Norm_add_le`, `l1Norm_split`,
`restrict_add_restrict_compl`, `norm_le_sqrt_card_mul_linfNorm`, `norm_restrict_le_of_subset`.
`CompressedSensing/Defs.lean` (DO NOT EDIT — laptop-only) defines `IsBasisPursuit`,
`IsUniqueBasisPursuit` and uses the cone `reCone S 1` (from `Lasso/Defs.lean`:
`reCone S α = {Δ | l1Norm (restrict Sᶜ Δ) ≤ α * l1Norm (restrict S Δ)}`) and `designMap X`.
`CompressedSensing/BasisPursuit.lean` has TWO theorems `:= by sorry`:
`deviation_mem_cone_of_basisPursuit` (A1) and `unique_basisPursuit_of_cone_trivial` (A2).

# TASK
Close ALL seven sorries (5 in VecNorms.lean + 2 in BasisPursuit.lean) to 0-sorry.

# PROOFS
## VecNorms bricks (all coordinatewise; mimic the existing proofs in the file)
- `l1Norm_add_le`: `l1Norm (x+y) = ∑ i, |(x+y).ofLp i|`; `(x+y).ofLp i = x.ofLp i + y.ofLp i`
  (try `simp` / `WithLp.ofLp_add` / `PiLp.add_apply`); then `Finset.sum_le_sum` with `abs_add`,
  and `Finset.sum_add_distrib`.
- `l1Norm_split`: rewrite both restrict ℓ¹ via `l1Norm_restrict_eq_sum`, then
  `Finset.sum_add_sum_compl S (fun i => |x.ofLp i|)` gives `∑_{i∈S} + ∑_{i∈Sᶜ} = ∑ i`.
- `restrict_add_restrict_compl`: prove `.ofLp`-pointwise (the two elements are equal iff their `.ofLp`
  agree — use the coordinate ext for `EuclideanSpace`/`WithLp`, e.g. `WithLp.toLp_ofLp`-style or
  `funext` after reducing to `.ofLp`); `simp [restrict_ofLp_apply, Finset.mem_compl]` then `split_ifs`.
- `norm_le_sqrt_card_mul_linfNorm`: `‖restrict S x‖ = √(∑ i, ((restrict S x).ofLp i)^2)`
  (`EuclideanSpace.norm_eq`); the summand is `0` off `S`, and `≤ (linfNorm (restrict S x))^2` on `S`
  (`abs_le_linfNorm` of `restrict S x`); bound `∑_{i∈S} c ≤ S.card • c` (`Finset.sum_le_card_nsmul`),
  then `Real.sqrt_le_sqrt` + `Real.sqrt_mul`. The existing `l1Norm_restrict_le_sqrt_card_mul_norm`
  is the structural template.
- `norm_restrict_le_of_subset`: square both sides via `EuclideanSpace.norm_eq`; the squared norm is
  `∑_{i∈S} (x.ofLp i)^2 ≤ ∑_{i∈T} (x.ofLp i)^2` by `Finset.sum_le_sum_of_subset_of_nonneg` (h, nonneg);
  then `Real.sqrt_le_sqrt`.
You MAY add small private helper lemmas to VecNorms.lean (it is in your touch-set), e.g.
`restrict_add : restrict S (x+y) = restrict S x + restrict S y`, `l1Norm_neg`,
`restrict_eq_self` (`(∀ i∉S, x.ofLp i = 0) → restrict S x = x`) — these make A1/A2 clean.

## A1 `deviation_mem_cone_of_basisPursuit`
Membership `(βhat-βstar) ∈ reCone S 1` unfolds (after `one_mul`) to
`l1Norm (restrict Sᶜ (βhat-βstar)) ≤ l1Norm (restrict S (βhat-βstar))`. From `hbp.1`:
`designMap X βhat = designMap X βstar`; from `hbp.2` applied to `βstar` (feasible by `rfl`):
`l1Norm βhat ≤ l1Norm βstar`. Set `Δ = βhat - βstar`, so `βhat = βstar + Δ`. Using `l1Norm_split S`
on `βhat`, `restrict_add`, `restrict Sᶜ βstar = 0` (from `hsupp`), and reverse triangle
`l1Norm a - l1Norm b ≤ l1Norm (a+b)` (from `l1Norm_add_le` + `l1Norm_neg`):
`l1Norm βstar ≥ l1Norm βhat ≥ l1Norm (restrict S βstar) - l1Norm (restrict S Δ) + l1Norm (restrict Sᶜ Δ)`
`= l1Norm βstar - l1Norm (restrict S Δ) + l1Norm (restrict Sᶜ Δ)`  (since βstar supported on S),
hence `l1Norm (restrict Sᶜ Δ) ≤ l1Norm (restrict S Δ)`.
RECOMMENDED: factor the private inner lemma
`mem_cone_of_feasible_of_le : designMap X β = designMap X βstar → (∀ i∉S, βstar.ofLp i = 0)
   → l1Norm β ≤ l1Norm βstar → (β - βstar) ∈ reCone S 1`
and derive A1 from it (with `β := βhat`).

## A2 `unique_basisPursuit_of_cone_trivial`
`IsUniqueBasisPursuit = ⟨IsBasisPursuit, uniqueness⟩`.
- Uniqueness clause `∀ β, designMap X β = designMap X βstar → l1Norm β ≤ l1Norm βstar → β = βstar`:
  by `mem_cone_of_feasible_of_le`, `Δ = β-βstar ∈ reCone S 1`; also `Δ ∈ ker (designMap X)`
  (`designMap X Δ = designMap X β - designMap X βstar = 0`, `map_sub`); so `Δ ∈ reCone S 1 ∩ ker = {0}`
  by `htriv`, giving `Δ = 0`, i.e. `β = βstar` (`sub_eq_zero`).
- `IsBasisPursuit`: feasibility is `rfl`; minimality `∀ β feasible, l1Norm βstar ≤ l1Norm β` by
  `by_cases l1Norm β ≤ l1Norm βstar` — if so, uniqueness gives `β = βstar` so equal; else
  `le_of_not_le`.

# REQUIREMENTS
ZERO sorry. Every theorem hypothesis already carries a `-- USER-INPUT:`/`-- LEAN-ONLY:` tag — keep them.
Do not weaken or add hypotheses to the seven target signatures. Do not touch `Defs.lean`, the area
umbrella, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, or any file outside the touch-set.

# TOUCH-SET: ONLY
  StatLean/HighDimensionalStatistics/ForMathlib/VecNorms.lean
  StatLean/HighDimensionalStatistics/CompressedSensing/BasisPursuit.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.CompressedSensing.BasisPursuit
# DONE = build exits 0; `lake build ... 2>&1 | grep -c sorry` is 0 for these two files; commit
  (`cs(base): VecNorms bricks + basis-pursuit cone lemmas (Lu-BDA ch6)`).
  Report: build status, sorry count, any added helper lemmas, any deviation from the stated lemmas.
