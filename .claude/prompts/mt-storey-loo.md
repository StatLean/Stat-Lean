# mt-storey-loo — close storey_fdr_le via the BH leave-one-out machinery (Candès L7 §7.4)

You are a Lean 4 proof subagent on branch `mt/storey-loo` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain `lake build`,
ITERATE to a GREEN build (exit 0, no tactic errors). Never `lake update`.

## The key idea (this REPLACES the backwards-martingale approach)
`storey_reverseMG_ost` (a continuous backwards-martingale OST) is **Mathlib-absent and should be
abandoned**. Instead, prove `storey_fdr_le` by the **leave-one-out independence** technique that
`BHMartingale.lean` already uses to prove `benjamini_hochberg_fdr_eq` 0-sorry — no martingale, just
`IndepFun` factorization, which Mathlib has. Storey's FDP has the SAME summand shape as BH.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Storey.lean`

You MAY delete `storey_reverseMG_ost` and its helpers if the leave-one-out proof makes them unused.
Keep the procedure defs (`storeyPiZero`/`storeyFDRhat`/`storeyThreshold`/`storeyRejects`) and the
public `storey_fdr_le` signature. `storey_binom_bound` and `storey_threshold_attained` are already
proved — reuse them.

## READ FIRST — the template you are mirroring
`StatLean/MultipleTesting/BHMartingale.lean` (the WHOLE file, 656 lines, 0-sorry). The proof skeleton
of `benjamini_hochberg_fdr_eq` (line 630) is:
1. `fdp_eq_sum_div` (617): `FDP = ∑_{i∈H₀} 𝟙(i∈Rej)/(R∨1)`.
2. `integral_finset_sum` + `integrable_bh_summand` (313): swap `∫` and `∑`.
3. `bh_claim_eq` (476): each summand integral `∫ 𝟙(i∈Rej)/(R∨1) dμ = α/N`, proved via
   **`bh_loo_indep_mul` (348)**: setting `pᵢ := 0` (`Function.update p i 0`) makes the rejection
   count depend only on the OTHER coordinates, so `pᵢ ⊥ R_loo` and
   `μ({pᵢ≤t}∩{R_loo=k}) = μ{pᵢ≤t}·μ{R_loo=k}` (`IndepFun.measure_inter_preimage_eq_mul`); combined
   with `bhCount_loo_eq_of_ge` (120, the loo-count monotonicity) and `bh_mem_imp_le` (412, the
   forward crux `pᵢ≤R·α/N`).
4. Sum: `∑_{H₀} α/N = (N₀/N)α`.

## Storey analogues to build (mirror each BHM lemma)
- `storey_fdp_eq_sum_div` ↤ `fdp_eq_sum_div`: `FDP H₀ (storeyRejects p q) ω = ∑_{i∈H₀} 𝟙(i∈storeyRejects)/(R(τ)∨1)`
  (you already have `storey_FDP_eq`; turn the `nullCountLE` numerator into the `∑ 𝟙` form via
  `numFalseRejections_eq_sum` analogue).
- `storey_loo_indep_mul` ↤ `bh_loo_indep_mul`: with `pᵢ := 0`, `pᵢ ⊥ (storeyThreshold/R/V computed
  from `Function.update p i 0`)`. **Same proof** (`hindep.indepFun_finset {i} {i}ᶜ`, the `recon`
  reconstruction, `IndepFun.measure_inter_preimage_eq_mul`).
- `storey_claim_le` ↤ `bh_claim_eq`: the per-null summand bound. **This is where Storey differs from
  BH**: at the threshold `τ`, `storey_threshold_attained` gives `storeyFDRhat q τ ω ≤ q`, i.e.
  `π̂₀·n·τ/(R(τ)∨1) ≤ q`, so the summand `𝟙(pᵢ≤τ)/(R(τ)∨1) ≤ q·𝟙(pᵢ≤τ)/(π̂₀·n·τ)`. Take `∫`, use the
  leave-one-out independence to factor `pᵢ` (uniform: `∫𝟙(pᵢ≤τ)·(…)` integrates `pᵢ` out to a `τ`/length
  factor), and reduce the remaining `R(1/2)` dependence (`π̂₀ = (1+n−R(1/2))/(n/2)`) using
  **`storey_binom_bound`** (the `V(1/2)~Bin(n₀,½)` law, already proved). Target:
  `∑_{i∈H₀} ∫ summand ≤ q`.
- `storey_fdr_le` ↤ `benjamini_hochberg_fdr_eq`: assemble (unfold `FDR`, `simp_rw`, swap, bound each
  summand, sum `≤ q`).

If the full per-null `storey_claim_le` resists, isolate the single hardest step as ONE named `sorry`
(far sharper than the whole `storey_reverseMG_ost`) — but aim for 0-sorry.

## Constraints
No `axiom`/`admit`/new public hypotheses; keep `-- USER-INPUT` tags + docstrings. Named
`private`/`theorem` helpers only. **Finish on `lake build … ` exit 0.** Commit to `mt/storey-loo`
(`mt(storey): close storey_fdr_le via BH leave-one-out (no backwards MG) (Candès L7 Thm 3)`).

## DONE
`lake build StatLean.MultipleTesting.Storey` exits 0. Report build status, final sorry count (0 = T6
fully closed), and which BHM lemmas you mirrored.
