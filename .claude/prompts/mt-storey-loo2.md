# mt-storey-loo2 — close storey_fdr_le via BH leave-one-out, DELETE the backwards MG (Candès L7 §7.4)

You are a Lean 4 proof subagent on branch `mt/storey-loo2` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` (§2,§6,§7,§9). In an `srun` allocation: plain `lake build`, ITERATE to GREEN (exit 0,
no tactic errors). Never `lake update`.

## HARD REQUIREMENT (a prior attempt failed by ignoring this)
**DELETE `storey_reverseMG_ost`, `storeyLHSint`, `storeyRHSint` and every backwards-/reverse-martingale
declaration.** The finished file must contain NO reverse-martingale, NO `condExp`, NO optional-stopping
on a continuous filtration. If `grep -i 'reverseMG\|backwards\|reverse.martingale'
StatLean/MultipleTesting/Storey.lean` returns anything but comments explaining the *replacement*, the
task is FAILED. `storey_fdr_le` must be proved entirely by the **leave-one-out independence** method.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Storey.lean`

Keep the procedure defs (`storeyPiZero`/`storeyFDRhat`/`storeyThreshold`/`storeyRejects`), the proved
`storey_binom_bound`, `storey_threshold_attained`, the FDP→counting lemmas, and the public
`storey_fdr_le` signature. Everything else is fair game to delete/rewrite.

## Template — READ THE WHOLE FILE `StatLean/MultipleTesting/BHMartingale.lean` (656 lines, 0-sorry)
`benjamini_hochberg_fdr_eq` is proved with NO martingale via: `fdp_eq_sum_div` → `integral_finset_sum`
(+`integrable_bh_summand`) → `bh_claim_eq` (per-null, via `bh_loo_indep_mul`+`bh_loo_le_imp_mem`+
`bhCount_loo_eq_of_ge`) → sum. Mirror each lemma for Storey.

## The proof (each step has a BHM analogue)
1. `storey_fdp_sum`: `FDP H₀ (storeyRejects p q) ω = ∑_{i∈H₀} 𝟙(pᵢ ≤ τ ω)/(R(τ ω) ∨ 1)`
   (`τ ω = storeyThreshold p q ω`, `R(t) = countLE p t`). [↤ `fdp_eq_sum_div`; you have `storey_FDP_eq`.]
2. **The leave-one-out indicator identity** `storey_loo_ind` (the crux — its validity is PROVEN below):
   with `p⁰ᵢ = Function.update p i 0` and `τ_loo ω = storeyThreshold p⁰ᵢ q ω`,
   `𝟙(pᵢ ω ≤ τ ω) = 𝟙(pᵢ ω ≤ τ_loo ω)` AND `R(τ ω) ω = countLE p⁰ᵢ (τ_loo ω) ω` on `{i ∈ storeyRejects}`.
   **Proof of the identity (do this case split):**
   - *Rejected* `pᵢ ≤ τ`: for `t ≥ pᵢ`, `countLE p t = countLE p⁰ᵢ t` (i is `≤ t` either way), so `FDRhat`
     agrees on `[pᵢ, 1/2]`; since `τ ≥ pᵢ`, the `sSup` is unchanged ⇒ `τ_loo = τ`. Both indicators `= 1`.
   - *Not rejected* `pᵢ > τ`: setting `pᵢ:=0` only changes `countLE` on `[0, pᵢ)`, lowering `FDRhat`
     there; on `[pᵢ, 1/2]`, `FDRhat` is unchanged and `> q` (as `τ < pᵢ`), so `τ_loo < pᵢ`. Both
     indicators `= 0`.
   [↤ `bh_loo_le_imp_mem` + `bhCount_loo_eq_of_ge`. This resolves the only obstruction; it DOES hold.]
3. `storey_loo_indep` ↤ `bh_loo_indep_mul`: `pᵢ ⊥ (τ_loo, countLE p⁰ᵢ ·)` since both are functions of
   `{p_j : j ≠ i}` only. Same proof (`hindep.indepFun_finset {i} {i}ᶜ`, `recon`,
   `IndepFun.measure_inter_preimage_eq_mul`).
3. `storey_claim_le` ↤ `bh_claim_eq`: per-null summand. Using (2), the summand
   `= 𝟙(pᵢ ≤ τ_loo)/(countLE p⁰ᵢ τ_loo ∨ 1)`. At `τ_loo`, the attainment (`storey_threshold_attained`)
   gives `storeyFDRhat q τ_loo ≤ q`, i.e. `π̂₀·n·τ_loo/(R_loo∨1) ≤ q`, so
   `1/(R_loo∨1) ≤ q/(π̂₀·n·τ_loo)`. Integrate `pᵢ` (uniform, ⊥ the loo-factor): `∫𝟙(pᵢ≤τ_loo)·(…) =
   E[τ_loo·(…)]`; the `τ_loo` cancels, leaving `≤ q·E[1/(π̂₀·n)] = q·E[1/(2(1+n₀−V(1/2)))]`-type, summed
   over `H₀` and bounded by `q` via `storey_binom_bound` (the `V(1/2)~Bin(n₀,½)` law). Target:
   `∑_{i∈H₀} ∫ summand ≤ q`.
4. `storey_fdr_le` ↤ `benjamini_hochberg_fdr_eq`: unfold `FDR`, `simp_rw` (1), `integral_finset_sum`,
   bound each summand by (3), sum `≤ q`.

If one mechanical step resists, isolate it as ONE named `sorry` — but it must be a LEAVE-ONE-OUT step
(measurability/integrability/algebra), NEVER a reverse-martingale. Aim for 0-sorry.

## Constraints
No `axiom`/`admit`/new public hypotheses; keep `-- USER-INPUT` tags. Named `private`/`theorem` helpers.
**Finish on `lake build … ` exit 0.** Commit to `mt/storey-loo2`
(`mt(storey): close storey_fdr_le 0-sorry via BH leave-one-out, delete backwards MG (Candès L7 Thm 3)`).

## DONE
`lake build StatLean.MultipleTesting.Storey` exits 0; `grep -c reverseMG Storey.lean` returns 0 (or
comment-only). Report build status, final sorry count, and that no martingale remains.
