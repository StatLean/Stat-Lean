# compr1 — SHARED RULES (Batch: comp/r1-* lanes off comp/round1)

> Milestone: Gentle, *Elements of Computational Statistics* (2002) ch. 2–4 — the new
> `StatLean/ComputationalStatistics/` area, Round 1. All target files exist as
> statement-first stubs (green with sorries at the stub gate).
> Notes: `notes/computational_statistics/round1/` (do NOT edit).

## CRITICAL — how this session works

**THERE IS NO WAKEUP AND NO NOTIFICATION — this is a single non-interactive `claude -p`
run. If you stop issuing tool calls the session ENDS IMMEDIATELY and every uncommitted
line is swept into an unverified auto-commit.** Never "wait" for anything.

**How to build:** run `lake build <Module>` as an ordinary FOREGROUND command and read its
output in the same step. Never background a build, never `&`, never `srun`/`sbatch` (you
are already inside an srun allocation). Plain `lake build`.

## Environment

- Lean `v4.29.1`, Mathlib pinned at `5e932f97` — prebuilt under `.lake/packages/mathlib`
  (symlinked shared cache). **NEVER run `lake update`.**
- Forbidden surfaces (do not create/modify): `lakefile.lean`, `lake-manifest.json`,
  `lean-toolchain`, `notes/`, `StatLean.lean`, `StatLean/ComputationalStatistics.lean`,
  any `*/Defs.lean`, and every file outside YOUR touch-set (listed in the lane prompt).
- There is no `tools/` directory in this worktree. Search with: `exact?`/`apply?`/`rw?`
  in-proof; `rg -n '<pattern>' StatLean/` for our own lemmas FIRST;
  `rg -n '<pattern>' .lake/packages/mathlib/Mathlib/ -g '*.lean'` for Mathlib.
  Mathlib names describe the statement, not the folk name.

## Hard rules

1. **Statements are FROZEN.** Fill `sorry` bodies and add same-file `private` helpers
   only. You may add `import`/`open` lines at the top of YOUR touch-set files if needed.
   Never change a signature, hypothesis, docstring, or definition. If a statement looks
   unprovable as stated, **STOP work on it and write the precise obstruction (ideally a
   counterexample) into `LANE-REPORT.md` at the worktree root** — do not weaken it, do
   not add hypotheses.
2. Prove from the mathematics using pinned Mathlib + already-present StatLean lemmas.
   Sorried theorems from OTHER lanes' files may be used freely (they compile; the final
   round gate closes everything). **NEVER copy code from any external source.**
3. **Commit after each closed theorem**: `git add -A && git commit -m "compr1: close <name>"`.
4. **Time-box ~25 min per target, hard cap ~45 min.** If stuck: leave the `sorry`, move
   on, and record the obstruction in `LANE-REPORT.md`.
5. Keep lines ≤ 100 chars (repo lint). Match the surrounding comment/docstring style.
6. After closing a headline target, run `#print axioms <name>` in a scratch section and
   confirm only `propext, Classical.choice, Quot.sound` (then delete the scratch line).

## Pin-verified names (trust these over guesses)

- `MeasureTheory.measurePreserving_eval (μ) (i) : MeasurePreserving (fun x => x i)
  (Measure.pi μ) (μ i)` and `ProbabilityTheory.iIndepFun_pi (mX : ∀ i, AEMeasurable
  (X i) (μ i)) : iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)` — both in the pin.
- `Measure.pi_map_pi` — pushforward of `Measure.pi` under coordinatewise maps.
- `MeasureTheory.integral_toReal_rnDeriv_mul (hμν : μ ≪ ν) : ∫ x, (μ.rnDeriv ν x).toReal
  * f x ∂ν = ∫ x, f x ∂μ` (module `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`).
- `ProbabilityTheory.strong_law_ae_real` (module `Mathlib.Probability.StrongLaw`),
  `ProbabilityTheory.IndepFun.variance_add/variance_sum`, `ProbabilityTheory.variance`,
  `ProbabilityTheory.covariance`.
- `MeasureTheory.Measure.infinitePi` + `IsProbabilityMeasure` instance (module
  `Mathlib.Probability.ProductMeasure`); finite marginals via `Measure.infinitePi_pi`.
- `MeasurableEquiv.piFinSuccAbove` and its `Measure.pi` measure-preservation (search
  `piFinSuccAbove` in `Mathlib/MeasureTheory/Constructions/Pi.lean`).
- `Fin.sum_univ_succAbove : ∑ i, f i = f p + ∑ i, f (p.succAbove i)`.
- `MeasureTheory.integral_dirac'` (needs `StronglyMeasurable`), `integral_smul_measure`,
  `MeasureTheory.integral_finset_sum_measure`, `lintegral_dirac'`.
- ℝ≥0∞ hygiene: `ENNReal.toReal_inv`, `ENNReal.toReal_natCast`,
  `ENNReal.inv_mul_cancel`, `ENNReal.ofReal_sum_of_nonneg`,
  `ofReal_integral_eq_lintegral_ofReal`. Split-module gotchas:
  `Mathlib.MeasureTheory.Integral.Lebesgue` → `…Lebesgue.Basic`;
  `lintegral_prod_mul`/`lintegral_lintegral_swap` in `Mathlib.MeasureTheory.Measure.Prod`.
- Lint: `show` that changes the goal is forbidden — use `change`.

## Gate (before finishing)

Run `lake build <the modules in your lane prompt>` (foreground) and **paste the tail of
its output** into your final report. It must be green (0 errors); sorries allowed ONLY as
reported obstructions in `LANE-REPORT.md`. Then report per-target: `closed` /
`left-as-debt (why)`, plus the final sorry count of your touch-set files.
Finish with `git add -A && git commit -m "compr1 <lane>: <summary>"`.
