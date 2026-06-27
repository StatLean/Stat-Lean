# Close 2 tractable residuals: Pinsker KL-2cell DPI + Yang-Barron log-N

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.
CRITICAL: do NOT increase the sorry count of any file. Close the single named residual, or leave it unchanged.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/PinskerInequality.lean` (close `klDiv_ge_two_mul_tvDist_sq`)
- `StatLean/Minimaxity/Fano/YangBarron.lean` (close the `klDiv P (mixture) ≤ klDiv P (component) + log N` step)
The scalar Bernoulli Pinsker is ALREADY closed; only these two remain.

## 1. `klDiv_ge_two_mul_tvDist_sq`: `2·tvDist(μ,ν)² ≤ klDiv ν μ`
Partition `A = {x | q(x) ≥ p(x)}` (p,q densities vs ξ=μ+ν; `measurableSet_le`). The 2-point map
`f = A.indicator` pushes to Bernoulli. Data-processing: `klDiv (ν.map f) (μ.map f) ≤ klDiv ν μ`. Search
Mathlib for the DPI lemma: `./tools/loogle.sh '"klDiv"'` then look for `klDiv_map_le`/`klDiv_comp`/
`le_klDiv`/`klDiv.*map`; ALSO try `fDiv` data-processing (`fDiv_map_le`?). If NO ready DPI lemma exists,
compute directly: `ν.map f = Bernoulli (ν A)`, `μ.map f = Bernoulli (μ A)` on `Bool`, and
`klDiv (Bernoulli b) (Bernoulli a) = b log(b/a) + (1-b)log((1-b)/(1-a))` ≥ `2(a-b)²` by the already-closed
`bernoulli_pinsker_scalar`. The push-forward KL ≤ original KL is the only DPI step; if truly unavailable,
prove the 2-point case directly via `klDiv` on `Bool` measures (`klDiv_eq_integral_llr`, sum over `Bool`).
`tvDist μ ν = ν A - μ A` (or `|μ A - ν A|`) by the optimal-set characterization (`tvDist_eq_half_lintegral`
is CLOSED — use it).

## 2. YangBarron log-N step: `klDiv (Q j) ((1/N)Σ_k γ_k) ≤ klDiv (Q j) γ_{k(j)} + log N`
`(1/N)Σγ ≥ (1/N)·γ_{k(j)}` ⇒ `rnDeriv (Qj) ((1/N)Σγ) ≤ N·rnDeriv (Qj) γ_{k(j)}` (rnDeriv antitone in 2nd
measure: `Measure.rnDeriv_mono`/`rnDeriv_le_of_le` — search). Then `klDiv (Qj) mix = ∫ log(rnDeriv (Qj) mix) dQj
≤ ∫ log(N · rnDeriv (Qj) γ) dQj = log N + klDiv (Qj) γ` (`klDiv_eq_integral_llr`, `Real.log_mul`,
`integral_add`). `klDiv_mixture_minimizes` is CLOSED. Handle ac side-conditions.

## DONE: build both modules green; `git add` only the two files; commit `mmx(batch9): close Pinsker DPI + YangBarron`.
Report which closed. If one resists after honest effort, leave its single sorry UNCHANGED (do not split).
