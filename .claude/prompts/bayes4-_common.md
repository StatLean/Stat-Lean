# bayes4 — SHARED RULES (Batch: bay/bvm-*, bay/bpe-*, bay/doob-*)

> Milestone: vdV *Asymptotic Statistics* (1998) Chapter 10 — Bernstein–von Mises (Thm 10.1),
> exponentially powerful tests (Lemma 10.3), Bayes point estimators (Thm 10.8), Doob
> consistency (Thm 10.10), efficient-centering corollary (p. 144).
> Notes: `notes/bayesian/batch4/` (do NOT edit).

## CRITICAL — how this session works

**THERE IS NO WAKEUP AND NO NOTIFICATION — this is a single non-interactive `claude -p`
run. If you stop issuing tool calls the session ENDS IMMEDIATELY and every uncommitted line
is swept into an unverified auto-commit.** (A previous campaign lost three sessions to
"I'll wait for the build notification… standing by." Do not be the fourth.)

**How to build:** run `lake build <Module>` as an ordinary FOREGROUND command and read its
output in the same step. Never background a build, never `&`, never poll with `until pgrep`,
never `srun`/`sbatch` (you are already inside an srun allocation). Plain `lake build`.

## Environment

- Lean `v4.29.1`, Mathlib pinned at `5e932f97` — prebuilt under `.lake/packages/mathlib`
  (symlinked shared cache). **NEVER run `lake update`.**
- Forbidden surfaces (do not create/modify): `lakefile.lean`, `lake-manifest.json`,
  `lean-toolchain`, `notes/`, `StatLean.lean`, `StatLean/Bayesian.lean`,
  `StatLean/AsymptoticStatistics.lean`, any `*/Defs.lean`, and every file outside YOUR
  touch-set (listed in the lane prompt).
- The repo CLAUDE.md is not in this worktree — everything you need is in this prompt.

## Hard rules

1. **Statements are FROZEN.** Fill `sorry` bodies and add same-file `private` helpers only.
   You may add `import` lines and `open` lines at the top of YOUR touch-set files if needed.
   Never change a signature, hypothesis, docstring, or definition. If a statement looks
   unprovable as stated, **STOP work on it and report precisely why** — do not weaken it,
   do not add hypotheses.
2. Prove from the mathematics using pinned Mathlib + already-closed StatLean lemmas.
   **NEVER copy code from any external source.**
3. **Commit after each closed theorem**: `git add -A && git commit -m "close <name>"`.
4. **Time-box ~25 min per target, hard cap ~45 min.** If stuck: leave the `sorry`, move to
   the next target, and report the obstruction at the end.
5. Keep lines ≤ 100 chars (repo lint).
6. After closing a headline target, run `#print axioms <name>` in a scratch section and
   confirm only `propext, Classical.choice, Quot.sound` (then delete the scratch line).

## Search / tactics

- `exact?` / `apply?` / `rw?` first.
- `./tools/where.sh '<name>'` — check whether StatLean already has it (instant, offline).
- `./tools/loogle.sh '"substring"'` or type patterns; `./tools/check.sh '<exact.name>'`.
- Names in this prompt were verified against the pin — trust them over guesses.
- Inner products: `⟪a,b⟫_ℝ` reduces via `RCLike.inner_apply` with a `mul_comm` flip; for
  plain reals use `change a * b = b * a; ring`.
- After `lintegral_map` / `Measure.compProd_apply` / `Measure.prod_apply`, integrands are
  un-β-reduced — use `simp_rw` or `change` before the next `rw`.
- ℝ≥0∞ hygiene: stay in `lintegral`/`ofReal`; bridges:
  `ofReal_integral_eq_lintegral_ofReal`, `ENNReal.toReal_le_toReal`, `ENNReal.div_le_iff`,
  `ENNReal.mul_div_mul_left`, `ENNReal.ofReal_le_ofReal_iff`, `tsub` lemmas
  (`tsub_le_iff_right`, `ENNReal.sub_eq_zero_iff_le`... check names with loogle).
- Split-module gotchas on this pin: `Mathlib.MeasureTheory.Integral.Lebesgue` →
  `…Lebesgue.Basic`; `lintegral_lintegral_swap`/`lintegral_prod_mul` live in
  `Mathlib.MeasureTheory.Measure.Prod`; `EuclideanSpace`/`stdOrthonormalBasis` in
  `Mathlib.Analysis.InnerProductSpace.PiL2`.

## Gate (before finishing)

Run `lake build <the modules listed in your lane prompt>` (foreground) and **paste the tail
of its output** into your final report. It must be green (0 errors); sorries allowed ONLY
where your lane prompt sanctions a named debt. Then report per-target:
`closed` / `left-as-debt (why)`, plus the final sorry count of your touch-set files.
Finish with `git add -A && git commit -m "bayes4 <lane>: <summary>"`.
