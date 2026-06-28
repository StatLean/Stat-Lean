# mt-rank-uniform — exchangeability ⇒ rank uniformity (Candès L9 §9.6)

You are a Lean 4 proof subagent on branch `mt/rank-uniform` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE. Never `lake update`. **Time-box**; if the symmetry bookkeeping resists
after real effort, leave `measure_rankOf_le` as the single named `sorry` (see DONE).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/RankUniform.lean`

Do **not** change the `def rankOf` / `def Exchangeable` signatures (downstream `Conformal/Coverage`
depends on them). You MAY add `private` helper lemmas. Do not touch other files.

## Goal
Prove `measure_rankOf_le` (0-sorry ideal). `lake build StatLean.MultipleTesting.ForMathlib.RankUniform` green.

## The theorem
`S₀,…,S_{m-1}` exchangeable + a.s. distinct ⟹ `μ{ rankOf S i ≤ k } = k/m` for `k ≤ m`, where
`rankOf S i ω = #{ j : Sⱼ(ω) ≤ Sᵢ(ω) }`.

## Proof roadmap (symmetry / counting)
1. **Equivariance** (`private`): for `σ : Equiv.Perm (Fin m)`,
   `rankOf (fun i => S (σ i)) i ω = rankOf S (σ i) ω`. Proof: the filtered set
   `{j | S(σ j) ω ≤ S(σ i) ω}` has the same card as `{j' | S j' ω ≤ S(σ i) ω}` by reindexing along
   the bijection `σ` (`Finset.card_bij`/`Finset.card_nbij'`/`Equiv.Perm` image, or
   `Finset.card_image_of_injective` after `filter_map`).
2. **Rank-prob independent of `i`**: `μ{ rankOf S i ≤ k } = μ{ rankOf S j ≤ k }` for all `i,j`.
   The event `{ω | rankOf S i ω ≤ k} = (fun ω => fun l => S l ω) ⁻¹' Aᵢ` where
   `Aᵢ = {t : Fin m → ℝ | #{l | t l ≤ t i} ≤ k}` is measurable. Using `Exchangeable` with the
   transposition `σ = Equiv.swap i j` and `Measure.map_apply`, transport `μ(Tmap ⁻¹' Aᵢ)` to
   `μ(Tmap ⁻¹' A_{σ i})` (combine with step 1's equivariance). Conclude all `μ{rankOf S i ≤ k}` are
   equal; call the common value `q k`.
3. **A.s. the ranks are a bijection** (`private`): on the a.s. set where `i ↦ S i ω` is injective,
   `i ↦ rankOf S i ω` is a bijection `Fin m → {1,…,m}` (strictly: `rankOf S · ω` is injective and
   lands in `Finset.Icc 1 m`). Hence for each `r ∈ {1,…,m}`, `∑_i 𝟙(rankOf S i ω = r) = 1` a.e.
   (`Finset.card_eq_one` / the bijection gives exactly one `i` with each rank).
4. **Count**: integrate step 3: `∑_i μ{rankOf S i = r} = ∫ ∑_i 𝟙(rankOf S i = r) dμ = ∫ 1 = 1`.
   With all terms equal (step 2, applied to the event `{= r}` via `{≤ r} \ {≤ r-1}`):
   `m · μ{rankOf S 0 = r} = 1`, so `μ{rankOf S i = r} = 1/m` (as `ℝ≥0∞`; `m ≥ 1` since `i : Fin m`).
   Then `μ{rankOf S i ≤ k} = ∑_{r=1}^{k} μ{rankOf S i = r} = k · (1/m) = k/m`
   (`measure_biUnion_finset` over the disjoint `{rankOf = r}`, or telescope `{≤ k}` into singletons).

(`m > 0` is available from `i : Fin m`: `Fin.pos i` / `Nat.pos_of_ne_zero`.)

## Lean guidance
- Measurability of `{ω | rankOf S i ω ≤ k}`: `rankOf` is a card-of-filter; mirror
  `ForMathlib/EmpiricalCDF.measurable_countLE` (sum-of-indicators via `Finset.card_filter`,
  `measurableSet_le (hmeas j) (hmeas i)`).
- `Measure.map_apply` needs measurability of the tuple map `fun ω => fun l => S l ω`
  (`measurable_pi_lambda`) and of `Aᵢ`.
- ℝ≥0∞ arithmetic: `ENNReal.div`, `ENNReal.natCast_*`; `m ≠ 0` for the division.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; any residual `sorry` must be the single top-level `measure_rankOf_le`. Commit to
`mt/rank-uniform` (`mt(rank): exchangeable ⇒ rank uniform μ{rank≤k}=k/m (Candès L9)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.RankUniform` exits 0. Report build status, sorry
count (0 ideal; if time-boxed, exactly 1 named sorry on `measure_rankOf_le` + one-line reason),
helpers added, and the route used for the symmetry step.
