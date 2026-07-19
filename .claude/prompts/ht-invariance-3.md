# Third pass: Invariance/{MaximalInvariant,UMPInvariantFinite} — the MeasurableSMul gap is now FIXED

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Build in order: `StatLean.HypothesisTesting.ForMathlib.GroupAverageMeasure`, then the three `Invariance` modules. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** those four files. Touch nothing else — NOT `Invariance/Defs.lean` or `Tests/Defs.lean` (frozen, laptop-only). `GroupAverageMeasure` keeps **Mathlib-only imports**.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false or under-hypothesized, STOP, leave it sorried, and report precisely what is missing — that is the desired outcome, and the previous session's report of exactly this kind was acted on (see below).
- Commit after each lemma compiles.
- After green: `#print axioms condExp_eq_groupAverage`, `#print axioms isInvariantTest_iff_factors` — expect only `propext, Classical.choice, Quot.sound`.

## What changed since the previous session (READ THIS)

**The `[MeasurableSMul G 𝓧]` gap you diagnosed has been FIXED.** The four statements you
identified — `map_maximalInvariant_eq_of_orbit`, `orbitAverage_eq_avg_translated_density`,
`isUMPInvariant_of_orbitAverage_ratio`, `exists_isUMPInvariant_of_finite_transitive` — now
carry `[MeasurableSMul G 𝓧]`, so `Measurable (g • ·)` is available and the density transport /
`integral_map` change of variables and the orbit-power invariance step all go through.
**Close all four.** `condExp_eq_groupAverage` is closed and axiom-clean; the NP layer
(`exists_mostPowerful`, `isMostPowerful_npTest`, the fundamental inequality) is closed too.

Still genuinely blocked, do NOT attempt: `isInvariantTest_iff_factors_measurable` (⇒) needs
measurable uniformization (Jankov–von Neumann) — leave it sorried with your existing note;
and `isUMAEquivariant_of_isUMPInvariant` waits on `power_acceptanceTest` in `Tests/Confidence`
(a different item) plus a measurable-slice restriction on competitors.

## Original brief follows

**`condExp_eq_groupAverage` has been FIXED and is now provable.** The previous session correctly refused it: the explicit `(m : MeasurableSpace 𝓧)` was capturing the implicit `[MeasurableSpace 𝓧]` of `invariantSets` inside `hm_inv`, so the hypothesis never forced `m ≤ m𝓧` and the conclusion was false (reflection-invariant Gaussian with a non-measurable symmetric set). The hypothesis now reads `s ∈ @invariantSets G 𝓧 _ m𝓧 _`, pinning the ambient instance. **Close it now** by the intended route recorded in the file: `groupAverage G f` is invariant hence `m`-measurable via `hm_inv` + `preimage_mem_invariantSets`; for `A ∈ m`, invariance of `A` and of `μ` gives `∫_A f(g·x) dμ = ∫_A f dμ` for each `g`; average over `g` and apply `ae_eq_condExp_of_forall_setIntegral_eq`. `IsFiniteMeasure μ` supplies the σ-finiteness `condExp` needs, and `m ≤ m𝓧` is now genuinely derivable from `hm_inv`.

## The four under-hypothesized `MaximalInvariant` statements

The previous session flagged four statements as missing measurability hypotheses and left them sorried rather than guessing. **Do the same analysis and report it precisely**: for each, say exactly which hypothesis is missing and what the minimal honest addition would be (e.g. `Measurable M`, or the book's structural condition that `x ↦ (M x, Y x)` is a `MeasurableEmbedding`). Do **not** add hypotheses yourself — signatures are frozen and the laptop session will apply the fix, exactly as it just did for `condExp_eq_groupAverage`. Close whatever does not need them.

## `UMPInvariantFinite` (3 blocked)

The previous session reported these blocked on `MeasurableSMul` plus the Neyman–Pearson layer. **`NeymanPearson.Lemma.exists_mostPowerful` is now CLOSED and axiom-clean**, as are `isMostPowerful_npTest` and the fundamental inequality — so the NP half of the blockage is gone. If `MeasurableSMul` is genuinely required, report that as a signature gap rather than working around it.

## `EquivariantConfidence` (2)

The dictionary iff and the stabilizer-invariance corollary are closed; the UMA transfer remains. Note the deliberate asymmetry: the source's part (i) is strictly weaker than the iff and does **not** convert back — keep them separate.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, and for every statement you leave open, the precise missing hypothesis.
