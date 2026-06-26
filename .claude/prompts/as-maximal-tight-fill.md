# as-maximal-tight-fill — close the last sorry: tight_supNorm_chaining_bound

You are a Lean 4 proof subagent on branch `as/maximal-tight` (CONTINUING prior work). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). In an `srun` allocation: plain `lake build`, ITERATE to
GREEN 0-sorry. Never `lake update`.

## State (a prior pass got us here)
`StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean` now has:
* `tight_maximal_inequality` (~L2262) — **PROVED** modulo the one lemma below (n=0 done; n≥1 delegates).
* `bracketing_dyadicComparison_le` — **PROVED 0-sorry**, the dyadic–Riemann step 3:
  `Σ_q ε_q·√log N_[](ε_q) ≲ J_[](δq)` for `ε_q = δq·2^{-q}`. REUSE this; do not redo it.
* The three leaves (all proved): `tight_chain_level_bound` (~L523), `tight_chain_telescope_bound`
  (~L633), `tight_envelope_truncation_bound` (~L672); plus `chaining_envelope_from_bracket` (~L1236),
  `chaining_l2_slice_pointwise_bound` (~L1193), and the existing laundered assembler
  `tight_chain_full_assembly_brick` (~L1005, uses the CRUDE bound + `hAbsorb`).

## Touch-set (edit ONLY this file) — close the single remaining `sorry`
`tight_supNorm_chaining_bound` (~L2226, the `sorry` at ~L2242):
```
∫⁻ ξ, supNormOver F (fun f => empiricalProcess P n (X·ξ) f) ∂μ
  ≤ 2·bracketingEntropyIntegral δq F P + 2·√n·∫⁻|Φ|·𝟙{δq√n<|Φ|} ∂P
```
for iid `X` (meas/iindep/idem/law in scope), envelope `Φ` (`IsEnvelope`/meas/`MemLp 2`), `δq>0`, `n≥1`.

## The wiring to fill (steps 1,2,4,5; step 3 is `bracketing_dyadicComparison_le`)
This is the chain-construction bookkeeping. Build it as named `private` sub-lemmas if that helps, but
keep it all inside this file and end 0-sorry.
1. **Dyadic bracket cover + midpoint maps.** For `q = 0,1,2,…` get a finite `ε_q`-bracket cover of `F`
   in `L²(P)` (`HasFiniteBracketingCover` from `bracketingEntropyIntegral δq F P < ⊤`… but note δq is a
   free scale here — derive finiteness at each `ε_q ≤ δq` from the bracketing-number being the `⨅`;
   if a cover doesn't exist at some scale the entropy integral is `⊤` and the RHS is `⊤`, so handle the
   `bracketingEntropyIntegral δq F P = ⊤` case by `le_top` FIRST). Define `π_q : F → (Ω→ℝ)` picking each
   `f`'s bracket lower/upper midpoint at scale `ε_q` (use `Classical.choice` on the cover membership);
   measurability of `ξ ↦ supNormOver` over the FINITE per-scale index set is what the leaf needs.
2. **Per-level bound.** The link `π_q f − π_{q-1} f` has `L²`-norm `≲ ε_{q-1}` and, after truncating the
   envelope at `√n·ε_q`, sup `≤ √n·ε_q/(1+√log(1+N_q))`; apply `tight_chain_level_bound` to the finite
   link-class ⇒ `S_q := ∫⁻ supNormOver F |G_n(π_q−π_{q-1})| ≤ K·ε_q·√log(1+N_q) =: B_q`.
3. **(done)** `Σ_q B_q ≤ K'·bracketingEntropyIntegral δq F P` from `bracketing_dyadicComparison_le`.
4. **Telescope.** `tight_chain_telescope_bound` with `S_q ≤ B_q` and step 3 ⇒ `Σ_q S_q ≤ K''·J(δq)`.
   The chained sum `Σ_q (π_q − π_{q-1})` reconstructs `supNormOver F G_n` minus the un-truncated tail
   (`π_q → f` in `L²` as `q→∞`; `π_0` is the coarsest bracket, absorbed in the `≤ 2J` constant).
5. **Envelope tail.** `tight_envelope_truncation_bound` ⇒ the `+ 2·√n·∫|Φ|𝟙{|Φ|>δq√n}` term.
6. **Combine** to `≤ 2·J(δq) + 2·√n·tail` (tune constants; the leaves carry their own `K`'s — propagate
   them and verify the final constant is `≤ 2` on each summand, or adjust `tight_maximal_inequality`'s
   stated constant if the honest constant differs — but its statement currently says `2`, so hit `2`).

Heavily reuse `tight_chain_full_assembly_brick`'s body for steps 1,2,4,5 — it does exactly this wiring
but discharges the `+1` via `hAbsorb`; replace that single `hAbsorb` step with the genuine
`bracketing_dyadicComparison_le`, which removes the need for `hAbsorb` entirely.

## Fallback
If one measurability/π_q-construction step resists, isolate it as ONE further named `private` `sorry`
lemma with a precise statement — but the goal is 0-sorry for the whole file.

## Constraints
No `axiom`/`admit`; do not touch `tight_maximal_inequality`'s statement or the leaves. **Finish on
`lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to
`as/maximal-tight` (`as(empirical): close tight_supNorm_chaining_bound — full dyadic-chaining wiring, 0-sorry`).

## DONE
`lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exits 0; **0 sorry**. Report build
status, final sorry count, and which leaves/helpers you wired.
