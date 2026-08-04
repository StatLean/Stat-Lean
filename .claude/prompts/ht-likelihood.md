# Close LikelihoodMethods/*.lean (Ch 14.4 — the asymptotic likelihood trinity)

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session. Work the files sequentially, committing each as it compiles.

## Hard constraints

- **Only edit** `StatLean/HypothesisTesting/LikelihoodMethods/{EstimatorUnderAlternatives,ScoreUnderAlternatives,UniformLAN,TrinityChiSquared}.lean`.
- Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — nine such reports have been acted on this campaign, five of them false statements caught with counterexamples. Reporting a false statement is the highest-value output you can produce.
- Commit after each lemma compiles.

## This is mostly ASSEMBLY over already-merged AsymptoticStatistics machinery

The heavy lifting — quadratic-mean differentiability, contiguity, Le Cam's third lemma, local asymptotic normality, the multivariate CLT and Cramér–Wold — is already in the repo, closed and merged. Read the exact signatures with `./tools/api.sh` (from the worktree root) on:

- `StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean` — `WeakConverges`, `Contiguous`, `MutuallyContiguous`, `weak_limit_under_Q_of_lecam_third` and its variants, `contiguous_of_asymptotically_log_normal`.
- `StatLean/AsymptoticStatistics/LocalAsymptoticNormality/*.lean` — `productMeasure`, the LAN expansion, `contiguous_local_alternatives`, the asymptotic-representation results.
- `StatLean/AsymptoticStatistics/Probability/ScoreCLT.lean` (or wherever `clt_finDim` lives) and `ForMathlib/{MultivariateCLT,CramerWold}.lean`.
- `StatLean/AsymptoticStatistics/DQM/Defs.lean` — `DifferentiableQuadraticMean` and `fisherInformation`.

## Targets

- `EstimatorUnderAlternatives` (Thm 14.4.1): an asymptotically-linear estimator's limit under local alternatives `θ₀ + h/√n` via contiguity. Match the repo's `WeakConverges`/`productMeasure` conventions exactly; the asymptotic-linearity expansion is a hypothesis, the limit is Le Cam's third lemma applied to it.
- `ScoreUnderAlternatives` (Cor 14.4.1): the normalized score `Zₙ = n^{-1/2}∑ score` converges under `P^n_{θ₀+h/√n}` to `N(I(θ₀)h, I(θ₀))`. Direct from the score CLT plus Le Cam's third lemma (the shift `I(θ₀)h` is the contiguity drift).
- `UniformLAN`: the sup-over-`|h|≤c` LAN-remainder lemma — `→P 0` under the quadratic envelope hypothesis already in the signature. This is the one genuinely new analytic piece; if it resists after a bounded number of build cycles it is the acceptable lifted-`private`-sorry candidate.
- `TrinityChiSquared` (Thm 14.4.2): Wald, Rao-score and likelihood-ratio statistics are asymptotically equivalent (differences `→P 0` under `θ₀`) and each `⇒ chiSquared s` in law. State the limit against `StatLean.MultipleTesting.chiSquared s`. The three statistics are local defs from the model's density/score data; keep the efficient estimator sequence HYPOTHESIZED with the expansion from `EstimatorUnderAlternatives`, exactly as the source does.

## Closed, axiom-clean — black boxes

everything in `AsymptoticStatistics` (merged long ago); `MultipleTesting.ForMathlib.ChiSquared`; and from this batch `ForMathlib.LindebergCLT`, `Tests.*`, `NeymanPearson.Lemma.*`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms trinity_asymptotically_equivalent`, and for anything left open the precise obstruction.
