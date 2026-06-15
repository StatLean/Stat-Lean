# mt-holm — prove Holm–Bonferroni FWER control

You are a Lean 4 proof subagent on branch `mt/holm` (based on `mt/area` + `mt/foundations`).
Project: **StatLean** — read its `CLAUDE.md` (§2, §6, §7).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/HolmBonferroni.lean`

Do **not** touch `FDP/Defs.lean`, `PValues/Defs.lean`, `ForMathlib/*` (consume, don't edit), the
umbrella, or any other file. You MAY reshape `holmCount`/`holmRejects`/`bonferroniRejects` and add
named helpers *within this file*, keeping them faithful to the Holm/Bonferroni procedures and the
public theorem statements/hypotheses unchanged.

## Goal
Prove `holm_rejects_true_null_imp`, `holm_fwer_le`, `bonferroni_fwer_le` (0 sorry, 0 error).
Verify: `lean-fasrc-build StatLean.MultipleTesting.HolmBonferroni` green.

## The theorem (Holm 1979 — NOT in Lu-BDA, which has only §17 Bonferroni)
If every null `pⱼ` (`j ∈ H₀`) is super-uniform, the Holm step-down procedure at level `α` has
`FWER ≤ α` (no independence needed). Bonferroni (cutoff `α/N`) gives `FWER ≤ (N₀/N)·α ≤ α`.

## Proof
**Deterministic crux** `holm_rejects_true_null_imp`: *if Holm rejects any true null then
`∃ j ∈ H₀, pⱼ ≤ α/N₀`* (`N₀ = |H₀|`). Reason: consider the first true null Holm rejects, at sorted
position `i` (1-indexed), cutoff `α/(N−i+1)`. Every hypothesis rejected before it is a non-null
(it's the *first* true null), so at most `N − N₀` rejections precede it: `i − 1 ≤ N − N₀`, hence
`N − i + 1 ≥ N₀`, so its p-value `≤ α/(N−i+1) ≤ α/N₀`. (With the 0-indexed `holmCount` cutoff
`α/(N−i)` this is the same statement.)

**Union bound**: `FWER = P(∃ j∈H₀, j rejected) ≤ P(∃ j∈H₀, pⱼ ≤ α/N₀) ≤ Σ_{j∈H₀} P(pⱼ ≤ α/N₀) ≤
N₀·(α/N₀) = α`, the last step by `SuperUniform` (`P(pⱼ ≤ α/N₀) ≤ α/N₀`).

**Bonferroni** is the same union bound with cutoff `α/N`: `FWER ≤ N₀·(α/N) = (N₀/N)·α`.

## Lean guidance
- `FWER H₀ R μ = μ {ω | (R ω ∩ H₀).Nonempty}`. The event `{∃ j∈H₀, j ∈ R ω}` ⊆ `{∃ j∈H₀, pⱼ ω ≤ c}`
  by `holm_rejects_true_null_imp`; `measure_mono` then a finite union bound
  (`measure_biUnion_finset_le` / `MeasureTheory.measure_biUnion_le`) over `H₀`.
- Convert `μ {pⱼ ≤ c} ≤ ENNReal.ofReal c` (from `SuperUniform`) and sum: `∑_{j∈H₀} ofReal (α/N₀) =
  N₀ • ofReal(α/N₀) = ofReal(N₀·(α/N₀)) = ofReal α`. Mind `ENNReal` arithmetic (`ENNReal.ofReal_le_ofReal`,
  `Finset.sum_le_sum`, `nsmul`).
- Order statistics: `orderStat`, `orderStat_monotone` from `ForMathlib/OrderStatistics` (proven in
  `mt/foundations`). The first-true-null counting argument is the deterministic core — take your
  time on it; restate `holm_rejects_true_null_imp` in whatever exact form is cleanest.
- `holm_fwer_le` needs `hH₀ : H₀.Nonempty` (so `N₀ ≥ 1`, `α/N₀` well-defined); it's a hypothesis.

## Constraints
No `axiom`/`admit`; keep tags + docstrings; no new hypotheses on the public theorems; named
sub-lemmas only. Commit to `mt/holm`.
