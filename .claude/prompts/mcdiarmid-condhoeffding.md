Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §9, §10, §13 (kernel
measurability gotcha). Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh`.
Never `lake update`. THIS IS A HARD ITEM — budget generously, search Mathlib THOROUGHLY first.

# GOAL
Create `StatLean/ConcentrationInequalities/McDiarmid/CondHoeffding.lean`
(namespace `StatLean.ConcentrationInequalities`) proving the **conditional Hoeffding MGF lemma**
that underlies McDiarmid's bounded-differences inequality (Lu *Big Data Analysis* §3.1 `McDiarmid`).

Target lemma (name it `condExp_hoeffding_mgf`): for a real random variable `Z` on `(Ω, μ)` and a
sub-σ-algebra `m ≤ mΩ`, if `Z` is conditionally bounded in an interval of length `c` given `m`
(i.e. there are `m`-measurable `A ≤ Z ≤ A + c` a.e., equivalently `Z − E[Z|m] ∈ [a,b]` with
`b − a = c` conditionally), then the conditional MGF obeys the Hoeffding bound
  `E[ exp(λ (Z − E[Z|m])) | m ] ≤ exp(λ² c² / 8)`   a.e., for all `λ : ℝ`.

# STRATEGY — search first, this may largely exist in Mathlib
1. **Check Mathlib's conditional sub-Gaussian API**: `./tools/loogle.sh '"HasCondSubgaussianMGF"'`,
   `./tools/loogle.sh '"condSubgaussian"'`, and read `Mathlib/Probability/Moments/SubGaussian.lean`
   around the conditional section. Mathlib has `ProbabilityTheory.Kernel.HasCondSubgaussianMGF`
   and azuma-type lemmas. There may be an existing `…condExp…hoeffding…` or a
   `hasCondSubgaussianMGF_of_…bounded` lemma. If a Mathlib lemma already gives the conditional
   Hoeffding MGF for conditionally-bounded variables, **the task is to state `condExp_hoeffding_mgf`
   in our vocabulary and close it by that lemma** (a wrapper), NOT to reprove Hoeffding.
2. If only the UNconditional Hoeffding-MGF (`hasSubgaussianMGF_of_mem_Icc`, used in our
   `SubGaussian/Bounded.lean`) plus the conditional-sub-Gaussian *structure* exist, build the
   conditional version: condition via `condExpKernel`, apply the per-fiber (kernel) bounded-MGF
   bound, integrate. Mathlib bricks: `condExpKernel`, `ProbabilityTheory.Kernel.HasSubgaussianMGF`,
   `MeasureTheory.condExp`, and the §13 kernel-measurability lemma `measurable_kernel_prodMk_left'`.

# HARD RULE — ZERO sorry is the bar for this branch.
The project owner requires this lemma fully proven (it was previously an accepted-debt fallback).
Spend the budget. If — after a thorough, documented effort — a TRULY irreducible Mathlib gap
remains, commit what compiles and leave EXACTLY ONE named `sorry` lemma `condExp_hoeffding_mgf`
with a precise docstring stating (a) the exact remaining goal, (b) which Mathlib lemmas you tried,
(c) why they did not close it. Print this prominently in your final report so the orchestrator can
escalate. Do NOT scatter sorries; do NOT weaken the statement to a vacuous one.

§2 tags: the conditional-bound hypothesis is `-- USER-INPUT: …; Lu-BDA §3.1`. Any measurability/
integrability regularity is `-- LEAN-ONLY: …`.

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/McDiarmid/CondHoeffding.lean`. Do NOT touch
any `Defs.lean`, the umbrella, `StatLean.lean`, lakefile/manifest/toolchain, `notes/`.

# BUILD
  srun -p shared -c 8 --mem=24G -t 1:00:00 lake build StatLean.ConcentrationInequalities.McDiarmid.CondHoeffding

# DONE = build exits 0; ZERO sorries (or exactly one named `condExp_hoeffding_mgf` if truly blocked);
§2 tags; small commits (`conc(mcdiarmid): conditional Hoeffding MGF (Lu-BDA §3.1)`). Final report
MUST state: did Mathlib already have it (which lemma), or did you build it; and the exact sorry
status. Independently re-verified.
