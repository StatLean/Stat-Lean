# mt-storey-cruxes — close the 3 Storey cruxes (Candès L7 §7.4)

You are a Lean 4 proof subagent on branch `mt/storey-cruxes` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`. **Goal: 0-sorry the whole file.** Close the 3 named
cruxes; `storey_fdr_le` is already assembled modulo them. Prioritize in the order below (1 and 2 are
tractable — secure them first; 3 is the hard one).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Storey.lean`

Read the whole file first. The 3 `sorry`s are `storey_binom_bound`, `storey_threshold_attained`,
`storey_reverseMG_ost`. All surrounding assembly is proved. Available bricks (read them):
`ForMathlib/SymmetricCondExp.lean` (i.i.d. fair-Bool exchangeable machinery — `signCount`, the
disintegration), `ForMathlib/BinomialRatio.lean` (`binom_ratio_sum_le_one`, proved),
`ForMathlib/EmpiricalCDF.lean`, `Knockoff/Supermartingale.lean` + `ForMathlib/OptionalStopping.lean`
(the discrete supermartingale OST pattern).

## Crux 1 — `storey_binom_bound` (TRACTABLE; do first)
The null indicators `Xⱼ = 𝟙(pⱼ ≤ 1/2)`, `j ∈ H₀`, are **i.i.d. fair Bool** (`P(pⱼ≤1/2)=1/2` from the
exact-uniform `hnull` at `t=1/2`; independent from `hindep`), and `V(1/2) = ∑_{j∈H₀} Xⱼ`. So
`V(1/2) ∼ Binomial(n₀,½)`: `μ{V(1/2)=k} = C(n₀,k)·2^{−n₀}` — prove by
`P(V=k) = ∑_{S⊆H₀,|S|=k} ∏_{j∈S}P(Xⱼ=1)∏_{j∉S}P(Xⱼ=0) = (#k-subsets)·2^{−n₀} = C(n₀,k)2^{−n₀}`
(`iIndepFun` factorization over the partition by `typeVec`/`signCount` in `SymmetricCondExp`, or a
direct `Finset.sum` over `{S : |S|=k}`). Then **LOTUS**: `∫ g(V(1/2)) dμ = ∑_{k=0}^{n₀} g(k)·μ{V=k}`
for the finite-range `V` (`integral` of a function of a `Fin`-valued / bounded-`ℕ`-valued r.v. =
`Finset.sum` over its range — `MeasureTheory.integral_finset_sum`-style or
`integral_eq_sum_of_...`). With `g(k)=k/(1+n₀−k)`, apply the proved `binom_ratio_sum_le_one` ⇒ bound.

## Crux 2 — `storey_threshold_attained` (MODERATE; do second)
`τ = sSup S`, `S = {t∈[0,1/2] : storeyFDRhat q t ω ≤ q}`. Show `storeyFDRhat q τ ω ≤ q` (the
attainment). Key: `countLE p · ω` is a **right-continuous** step function in the threshold (jumps up
at the `pⱼ`, constant on `[pⱼ, next)`), so `storeyFDRhat q · ω` is right-continuous and the sublevel
set's sup is attained. Use `0 ∈ S` (`storeyFDRhat q 0 = 0 ≤ q`, already `storeyThreshold_zero_mem`),
`bddAbove S`, and that `τ` equals one of finitely many candidate values (the `pⱼ ∧ 1/2`, or where the
linear-between-jumps part hits `q`). Reduce the `sSup` to a `Finset.max'` over the candidate
thresholds (`{pⱼ : pⱼ ≤ 1/2} ∪ {1/2}` and the per-gap solutions of `storeyFDRhat = q`), then check
membership directly — this sidesteps topological closedness. Mathlib: `Real.sSup_le`, `le_csSup`,
`csSup_mem` for compact/finite, `Finset.le_max'`.

## Crux 3 — `storey_reverseMG_ost` (HARD; the genuine core)
The backwards-martingale optional stopping `E[V(τ)/τ] = E[V(1/2)/(1/2)]`. **Discrete reformulation**
mirroring `Knockoff/Supermartingale.lean`: build the process over the sorted null order statistics
`θₖ = orderStat` restricted to `[0,1/2]`, with the **uniform-null conditional expectation** — the
analogue of `SymmetricCondExp.condExp_coord_eq_count_div`: for i.i.d. `Uniform[0,1]` nulls and
`s ≤ t`, `E[𝟙(Uⱼ≤s) | 𝒢_t] = (s/t)·𝟙(Uⱼ≤t)` a.e. (conditional on `{Uⱼ≤t}`, `Uⱼ ∼ Uniform[0,t]`, so
`P(Uⱼ≤s | Uⱼ≤t) = s/t`). Prove this uniform-condExp brick (the swap-invariance / disintegration is
the analogue of `measure_inter_swap_outer`), then assemble `M = V(t)/t` as a reverse martingale and
apply `supermartingale_integral_stoppedValue_le` (both directions for the equality, or the
martingale OST). The strict positivity from `storeyPiZero`'s `+1` gives integrability. **If this
resists after serious effort, isolate the single uniform-condExp lemma as the named `sorry`** and
prove `storey_reverseMG_ost` from it — that is real progress (1 sharper crux).

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + tags. Named `private`/`theorem` helpers only.
Commit to `mt/storey-cruxes` (`mt(storey): close binom-law + threshold-attain + reverse-MG cruxes`).

## DONE
`lake build StatLean.MultipleTesting.Storey` exits 0. Report build status, final sorry count + which
crux(es) closed vs remain, and (for crux 3) whether you reduced it to just the uniform-condExp lemma.
