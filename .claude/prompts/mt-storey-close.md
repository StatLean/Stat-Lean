# mt-storey-close — close the Storey reverse-martingale OST + FDR theorem (Candès L7 §7.4)

You are a Lean 4 proof subagent on branch `mt/storey-close` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`. **This is a research-level unit** — make real progress;
if a piece resists after serious effort, leave a SMALLER, sharper named `sorry` than what you started
with, and document exactly what remains.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Storey.lean`

It currently has 2 `sorry`s: `storey_reverseMG_ost` (the backwards-MG optional stopping) and
`storey_fdr_le` (the assembly). The procedure defs and the FDP→counting reduction
(`storey_FDP_eq`, `storey_numRejections_eq`, …) are already proved. Read the whole file.

## The goal & the template
Prove both theorems 0-sorry. The model is the **merged knock-off supermartingale development** —
READ these (they are the exact analogue, with *fair-coin* exchangeability where you need *uniform*):
- `StatLean/MultipleTesting/Knockoff/Supermartingale.lean` (discrete process over `orderStat` indices,
  natural filtration, hitting-time stopping, applies the OST bridge),
- `StatLean/MultipleTesting/ForMathlib/SymmetricCondExp.lean` (`condExp_coord_eq_count_div`:
  `E[𝟙(σᵢ)|count] = count/k` for i.i.d. fair Bool),
- `StatLean/MultipleTesting/ForMathlib/OptionalStopping.lean`
  (`supermartingale_integral_stoppedValue_le : ∫ stoppedValue f τ ≤ ∫ f 0`).

## Mathematical roadmap (discrete reverse martingale over null order statistics)
Let `U₁,…,U_{n₀}` be the null p-values (`n₀ = H₀.card`), i.i.d. `Uniform[0,1]`, independent of the
non-nulls. `V(t) = nullCountLE H₀ p t`. **Key probabilistic fact (the uniform analogue of
`condExp_coord_eq_count_div`):** conditional on `V(1/2) = m` (and the values `> 1/2`), the `m` nulls
that are `≤ 1/2` are i.i.d. `Uniform[0,1/2]`, so for `t ≤ 1/2`, `V(t) | V(1/2)=m ∼ Bin(m, 2t)`,
giving `E[V(t)/t | 𝒢_{1/2}] = 2m = V(1/2)/(1/2)` — the **reverse-martingale property**.

1. **`uniform_condExp` (the new hard brick)** — the uniform analogue of `condExp_coord_eq_count_div`:
   for `U : Fin k → Ω → ℝ` i.i.d. `Uniform[0,1]`, `s ≤ t`, and the count σ-algebra at level `t`,
   `E[𝟙(Uᵢ ≤ s) | σ(𝟙(U_· ≤ t), counts)] = (s/t)·𝟙(Uᵢ ≤ t)` a.e. Prove via the exchangeable
   disintegration (mirror `SymmetricCondExp.lean`'s structure: a swap-invariance `measure_inter_swap`
   argument, but on the uniform order statistics — `Uᵢ|Uᵢ≤t ∼ Uniform[0,t]`). **This is the crux;** if
   it resists, isolate it as the single named `sorry` and build the rest on it.
2. **Reverse-martingale + OST** — assemble the discrete process `M_k = V(θ_k)/θ_k` over the sorted
   null thresholds `θ_k = orderStat` (cf. Knockoff `Yproc`/`θ`/`tauStar`), show it is a martingale via
   (1), and apply the OST bridge to get `storey_reverseMG_ost`'s identity (you MAY restate
   `storey_reverseMG_ost` to the exact form `storey_fdr_le` consumes — keep it a faithful OST
   statement). The `+1`/strict-positivity of the denominator (from `storeyPiZero`'s `+1`) is what
   makes the stopped process integrable.
3. **`storey_fdr_le`** — assemble: `storey_FDP_eq` → threshold attainment `storeyFDRhat q τ ≤ q` (use
   right-continuity of `countLE` in `t`; the `sSup` is attained at a jump) → the OST identity →
   the binomial bound `E[V(1/2)/(1+n₀−V(1/2))] = 1−2^{−n₀} ≤ 1` via `V(1/2) ∼ Bin(n₀,½)` and
   `ForMathlib/BinomialRatio` (find the lemma with `./tools/api.sh
   StatLean/MultipleTesting/ForMathlib/BinomialRatio.lean`).

## Constraints
No `axiom`/`admit`/new hypotheses on the public theorems; keep docstrings + `-- USER-INPUT` tags.
Named `private`/named-`theorem` helpers only — any residual `sorry` must be a NAMED lemma (ideally
just the uniform-condExp brick). Commit to `mt/storey-close`
(`mt(storey): close reverse-MG OST + FDR≤q via uniform-null condExp (Candès L7 Thm 3)`).

## DONE
`lake build StatLean.MultipleTesting.Storey` exits 0. Report build status, final sorry count + WHICH
named lemma(s) remain (0 ideal; 1 = the uniform-condExp brick is a real win), the `BinomialRatio`
lemma used, and how far the discrete reverse-martingale assembly got.
