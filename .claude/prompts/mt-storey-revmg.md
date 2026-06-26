# mt-storey-revmg — close storey_reverseMG_ost (the backwards-MG OST) (Candès L7 §7.4)

You are a Lean 4 proof subagent on branch `mt/storey-revmg` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE to a GREEN build (the previous pass on a sibling crux left tactic errors by not
re-building at the end — **always finish on `lake build … ` exit 0**). Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Storey.lean`

This is the **last open Storey crux**: `storey_reverseMG_ost` (1 `sorry`). `storey_binom_bound`,
`storey_threshold_attained`, the FDP→counting reduction, and `storey_fdr_le` (modulo this) are all
proved. Read the whole file + the bricks below.

## The target
`storey_reverseMG_ost`: for independent exact-uniform null p-values,
`∫ V(τ)/τ dμ = ∫ V(1/2)/(1/2) dμ` where `V(t) = nullCountLE H₀ p t`, `τ = storeyThreshold p q`.

## Roadmap — discrete reverse martingale via the uniform conditional expectation
Model on the **merged knock-off development** (read it — it is the fair-coin analogue of exactly this):
- `StatLean/MultipleTesting/Knockoff/Supermartingale.lean` — discrete process over `orderStat`
  indices, natural filtration, hitting-time `τ`, applies the OST bridge.
- `StatLean/MultipleTesting/ForMathlib/SymmetricCondExp.lean` — `condExp_coord_eq_count_div`
  (`E[𝟙(σᵢ)|count]=count/k`) + the swap-invariance disintegration `measure_inter_swap*`.
- `StatLean/MultipleTesting/ForMathlib/OptionalStopping.lean` — `supermartingale_integral_stoppedValue_le`.

**Crux brick — the uniform conditional expectation** (the uniform analogue of
`condExp_coord_eq_count_div`): for i.i.d. `Uniform[0,1]` nulls `Uⱼ`, `s ≤ t`, and the count
σ-algebra `𝒢_t = σ(𝟙(U_·≤t))`,
`E[𝟙(Uⱼ ≤ s) | 𝒢_t] = (s/t)·𝟙(Uⱼ ≤ t)` a.e. **Proof** (mirror `SymmetricCondExp`): conditional on
`{Uⱼ ≤ t}`, `Uⱼ ∼ Uniform[0,t]` (the exact-uniform `hnull` + independence give
`μ({Uⱼ≤s}∩A) = (s/t)·μ({Uⱼ≤t}∩A)` for `A ∈ 𝒢_t` by a `measure_inter` rescaling), so the conditional
probability is `s/t`. Isolate this as a NAMED `private` lemma `uniform_condExp_indicator`.

Then: define `M_t = V(t)/t` over the relevant thresholds; the uniform-condExp brick gives the
reverse-martingale identity `E[M_s | 𝒢_t] = M_t` (`s ≤ t`); the strict positivity from `storeyPiZero`'s
`+1` keeps it integrable; apply `supermartingale_integral_stoppedValue_le` (both inequalities for the
equality, or the martingale form) at the stopping threshold `τ ≤ 1/2`. You MAY restate
`storey_reverseMG_ost` to whichever direction the OST bridge gives, as long as `storey_fdr_le` still
type-checks against it (rebuild to confirm).

## Graded outcome
- Best: `storey_reverseMG_ost` 0-sorry. Storey file fully closed.
- Real win: reduce it to the single named `uniform_condExp_indicator` lemma (1 sharper sorry) — that
  IS the irreducible probabilistic core, precisely isolated.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + tags. Named `private`/`theorem` helpers only.
**Rebuild to green before finishing.** Commit to `mt/storey-revmg`
(`mt(storey): close reverse-MG OST via uniform-null condExp (Candès L7 Thm 3)`).

## DONE
`lake build StatLean.MultipleTesting.Storey` exits 0. Report build status, final sorry count, and
whether you closed it fully or reduced it to `uniform_condExp_indicator`.
