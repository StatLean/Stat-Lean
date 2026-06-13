# CLAUDE.md — Project Charter

> Read this first at the start of every session. Written by/for AI collaborators.

## 1. Mission

**Formalize statistical theory in Lean 4 — the `StatLean` library.** The library is organized into per-area sublibraries under `StatLean/`, each with its own reference text, and results are reusable across areas:

* `StatLean/AsymptoticStatistics/` — asymptotic statistics. Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998). (`vdV §X.Y` in tags.)
* `StatLean/ConcentrationInequalities/` — sub-Gaussian / sub-exponential / Bernstein / maximal inequalities. Reference: Lu, *Big Data Analysis* ch. 2–4 (`ref/Lu_Big-Data-Analysis/`). (`Lu-BDA §X.Y` in tags.)
* `StatLean/HighDimensionalStatistics/` — OLS / Lasso statistical rates. Reference: Lu, *Big Data Analysis* ch. 5, 8. (`Lu-BDA §X.Y` in tags.)

Scope is open-ended; each area grows by adding theorems from its reference text. **The single `lean_lib` is `StatLean`** (root module `StatLean.lean`); each area has an umbrella `StatLean/<Area>.lean` that `StatLean.lean` imports.

> Note on book constants: textbook constants are sometimes off by small factors. State the constants that are actually *provable* and document any deviation from the book in the declaration's docstring.

## 2. Method

We treat this as **building a small mathematical library**, not patching together one-off proofs.

* **Build infrastructure ourselves.** Mathlib has no `score`, `Fisher information`, `differentiability in quadratic mean`, or related statistical-asymptotics primitives. We define them, prove their basic properties, and reuse across theorems. Style reference: [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory).
* **One concept per file.** Split aggressively. A file should answer "what is this file *about*" in one sentence. Files named after a single theorem ("Theorem7_2.lean") are fine for the *statement-and-assembly* of that theorem; the underlying machinery lives elsewhere.
* **Statement first, proof second.** When entering an unproven area, write the precise Lean statement of every sub-lemma in the dependency tree before filling any one of them. This makes the gap structure visible and lets us swap proof order without breaking downstream consumers.
* **Hypothesis discipline.** Every hypothesis in a theorem signature is a claim about what the caller must supply. Classify each as either a **genuine external input** (data, user free-choice — e.g. `M : ParametricFamily`, `hℓ : Measurable ℓ`, the statistic `T`) or something **mathematically forced by the setup parameters** (e.g. "multivariate CLT holds under `P^n_θ₀`"). The latter must be **derived internally** in the proof body, or **lifted to a named `sorry`'d theorem** in an appropriate file — never kept as a provider-pattern hypothesis. Lean's tooling (`lake build | grep sorry`, `#print axioms`) only catches **explicit** unproven content; a hypothesis argument is invisible to both, so hypothesis laundering produces misleading "clean compiles". Before claiming a main theorem done, run the **six-check audit** in [notes/hypothesis-discipline.md](notes/hypothesis-discipline.md) — Tier-0 mechanical (no stray sorry; clean `#print axioms`) plus main-theorem signature vs book (hypotheses, conclusion, instance constraints) plus transitive definitions vs book (structures and defs we authored).
* **Write-time PR rule (every commit, not just main theorems).** Each new `theorem` hypothesis gets a one-line `-- USER-INPUT: <claim>; <ref> §X.Y` (book input; `<ref>` ∈ {`vdV`, `Lu-BDA`}) or `-- LEAN-ONLY: <claim>; <why no scope change>` (Lean-side adapter) tag. Each new `structure` field gets an inline docstring marked `Constitutive (<ref> §X.Y): …` (book demands it; removal makes the object not the book's `X`) or moved out as a hypothesis (book allows objects without it = regularity, must NOT be a field). Each new `def` on a book-facing concept gets a docstring stating the book concept it formalizes + edge behavior (e.g. degenerate-input fallback). Missing any of these fails review — backlog forbidden. ~5 min/PR at write-time vs ~30+ min/PR if backfilled. Full rationale + worked examples in [notes/hypothesis-discipline.md](notes/hypothesis-discipline.md).
* **Stepwise, not heroic.** Don't try to do a whole theorem in one go. Pick one sub-lemma, do it cleanly, ship it, move on. Time-box anything that might not work.
* **`sorry` is a planned debt.** Each `sorry` should correspond to a *named, well-defined* sub-lemma. Don't sorry an arbitrary `have`; lift it to a top-level lemma so future sessions see the gap.

## 3. Directory conventions

```
StatLean/                      — the single lean_lib root (root module StatLean.lean)
├── AsymptoticStatistics.lean  — area umbrella (imported by StatLean.lean)
├── AsymptoticStatistics/      — area: asymptotic statistics (vdV)
│   ├── ForMathlib/            — pure math / probability, theorem-agnostic, candidate upstream
│   ├── ParametricFamily/      — concept layer (the family P_θ, scores, Fisher information)
│   ├── DQM/                   — concept layer (differentiability in quadratic mean)
│   └── ChN/ , Core/ , …       — chapter assembly: theorem-specific wiring
├── ConcentrationInequalities.lean   — area umbrella
├── ConcentrationInequalities/       — area: ch2–4 of Lu, Big Data Analysis
│   ├── SubGaussian/ , SubExponential/ , Bernstein/ , Maximal/ , McDiarmid/ , KDE/
└── HighDimensionalStatistics.lean   — area umbrella
    HighDimensionalStatistics/       — area: OLS MSE + Lasso rates (Lu ch5, ch8)
        ├── ForMathlib/ , LinearModel/ , OLS/ , Lasso/
```

Rules of thumb:

* **Three layers within each area, one-way dependency**: `ForMathlib/` → concept directories → assembly. Concept files never import assembly files; `ForMathlib/` never imports concept files.
* **Cross-area imports are allowed but directional.** A new area may import another area's `ForMathlib/` (bottom, Mathlib-only) layer — e.g. `HighDimensionalStatistics` imports `StatLean.ConcentrationInequalities.SubGaussian.*` for its noise bounds. The intended DAG is `…ForMathlib → ConcentrationInequalities → HighDimensionalStatistics`. Do **not** import another area's concept/assembly layer upward (that inverts the DAG; promote the shared piece to a `ForMathlib/` file instead). Each area's `ForMathlib/` stays under that area until a second area needs it, then promote lazily.
* **Concept files are theorem-agnostic**: adding a theorem touches its assembly file and maybe a concept lemma, never forcing an assembly dependency into a concept file.
* **Name files by concept, not by theorem** (the assembly file is the one place named after its target). Promote a general Step-K lemma out of assembly into the relevant concept directory.
* **One concept per file** — split aggressively once a file passes ~300 lines.
* **Import graph must remain a DAG.** Cycle = conflated concepts; split the file.
* Each area's umbrella `StatLean/<Area>.lean` imports every module in that area; `StatLean.lean` imports the umbrellas. New modules are added to their area umbrella by the **laptop session only** (see §10).
* See [notes/workflow.md §4.3](notes/workflow.md) for the core / assembly distinction that this layout structurally enforces.

## 4. Build commands

**This laptop cannot run `lake build`** (no local `.lake`, insufficient storage/compute). All builds run on FAS-RC via the `lean-on-fasrc` skill — see §10. Never run `lake` locally; never `lake update` anywhere.

```bash
# Build a specific module on the cluster (fastest gate):
lean-fasrc-build StatLean.AsymptoticStatistics.Core.EIF

# Build everything (default target = lean_lib StatLean):
LEAN_FASRC_TIME=0-03:00 lean-fasrc-build

# Cheapest smoke target:
lean-fasrc-build StatLean.AsymptoticStatistics.Core.Hilbert
```

A clean full build prints `Build completed successfully (~3321 jobs)`. Sorry warnings are expected on in-progress branches; **errors are not**. The build report prints the sorry count; the Mathlib payload (~3180 jobs) is the shared cache, so only project modules recompile.

## 5. Where to find current focus

This file (CLAUDE.md) intentionally **does not** track progress on individual theorems — that would rot fast and conflate "permanent project knowledge" with "today's status".

Status docs live under `notes/<area>/<milestone>/`. `ls notes/<area>/` is that area's roadmap. Current areas:

* `notes/concentration_inequalities/` — Lu ch2–4 (sub-Gaussian core, sub-exponential/Bernstein, McDiarmid, maximal/covering, KDE uniform rate) + `mathlib_bricks.md` (the verified Mathlib-name table for the pin).
* `notes/high_dimensional_statistics/` — OLS MSE (Lu ch5) and Lasso rates (Lu ch8).
* `notes/asymptotic_statistics/` — vdV theorem milestones (if/when revisited).

Each milestone gets its own `notes/<area>/<milestone>/` directory with `status.md` and `outline.md` following the same template: dependency tree, sub-lemma table (real / sorry), book-vs-Lean constants table, remaining hypotheses to discharge, next-step recommendations.

The single source of truth for *what's actually in the code* is `lake build`'s sorry inventory plus reading the file. The status docs describe *intent and progress*; they may lag the code.

## 6. Working with Claude — process conventions

See [notes/workflow.md](notes/workflow.md) for the full process. CLAUDE.md is the why/what; workflow.md is the how.

**Mathlib search tool priority** (Lean-specific, kept here because the search stack is not workflow-level):

* `exact?` / `apply?` / `rw?` inside a proof — zero friction, context-aware.
* `./tools/where.sh '<name-substring>'` (or `--doc '<text>'`) — **first check whether *we* already proved this in our own project before searching Mathlib.** Walks `StatLean/**/*.lean` for matching declarations. Pure shell, no network, instant.
* `./tools/check.sh '<exact.qualified.name>'` — verify a **known** name and see its signature.
* `./tools/loogle.sh '<pattern>'` — find a lemma by **type shape** (e.g. `|?a + ?b| ≤ _`).
* `./tools/loogle.sh '"substring"'` — find by **name substring** when you know a short name but not the full `Namespace.Sub.namespace.name` path (e.g. `'"IsMarkovKernel.map"'` returns `ProbabilityTheory.Kernel.IsMarkovKernel.map : …`). Prefer this over `Grep`-ing Mathlib for names.
  * ⚠️ **Caveat: Mathlib names describe the statement, not the folk name.** Searching `'"CentralLimit"'`, `'"LawOfLargeNumbers"'`, etc. will miss the actual declaration — e.g. the classical i.i.d. CLT is `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`, living in `Mathlib/Probability/CentralLimitTheorem.lean`, and `loogle` only matches the declaration name, not the module name. For folk/textbook names, skip this line and go straight to type-shape loogle or `explore.sh` / `#leansearch` below. A 0-hit substring search is **not** evidence of absence.
* `./tools/api.sh <lean-file>` — list a file's top-level declarations for orientation.
* `./tools/explore.sh "..."` — semantic / natural-language search via [LeanExplore](https://www.leanexplore.com). **First stop for folk/textbook names** (CLT, LLN, …) when `LEANEXPLORE_API_KEY` is set. Same query style as `#leansearch` but from the shell — no scratch `.lean` file. One-time setup: register at leanexplore.com (free) and `export LEANEXPLORE_API_KEY=...`.
* `#leansearch "..."` / `#moogle "..."` in a scratch `.lean` file — same kind of natural-language / concept search as `explore.sh`, but in-Lean. Use when no API key is set, or when results next to a Lean buffer are more convenient.
* Fallback when nothing above hits: `rg -n "..." .lake/packages/mathlib/Mathlib/ -g '*.lean'` (ripgrep has no built-in `lean` type, so `--type lean` errors out).
* Decision table: [tools/search.md](tools/search.md).

**⚠️ Before declaring "Mathlib has nothing" for a theorem-sized target:**
2–3 substring / type-shape loogle misses on the composite concept means stop searching the whole — it's usually not packaged under one name. Instead:

1. **Rewrite the goal in Mathlib-constructor language**, not folk math terms. "Girsanov for 1D Gaussian" becomes the identity `(gaussianReal 0 1).withDensity (…) = gaussianReal a 1` — each constructor (`gaussianReal`, `withDensity`, `map`) is now a search term.
2. **Decompose** into 2–5 atomic steps on paper. E.g. that Girsanov isn't in Mathlib, but `gaussianReal_of_var_ne_zero` (PDF form) + `withDensity_mul` + pointwise PDF algebra gives it in ~25 lines.
3. **Per-brick search**, cheapest first:
   - `./tools/api.sh <home-file>.lean` — scans a guessable file's declarations in <1s. Default when the concept's module is obvious (`Probability/Distributions/Gaussian/Real.lean`, `MeasureTheory/Measure/WithDensity.lean`, …). More reliable than guessing names.
   - `./tools/loogle.sh '"<root>"'` with naming roots: `_map_`, `_withDensity_`, `_of_`, `_eq_`, `_apply_`, `_integrable_`.
   - Type-shape loogle when names don't hit.
4. **Classify the result** as one of three states, not just yes/no:
   - **Directly supported** — same objects + operation + conclusion already in Mathlib.
   - **Composable** — ingredients exist; remaining gap is algebra / `Measure.ext` / coercion / standard side-conditions. Assemble them; if a brick is reusable, extract it as a `ForMathlib`-layer lemma.
   - **Not found** — no direct theorem *and* no sufficient ingredients. "No name match" alone is not enough to pick this bucket.
5. **State scope explicitly** (1D vs finite-dim vs path-space). A finite-dim theorem does not imply a process-level theorem.

## 7. Lean gotchas worth remembering

These cost us time at least once. Save the next session 30 minutes by knowing them.

1. **`set` does not auto-unfold.** After `set f := ...`, downstream tactics often need explicit `unfold` or `show` to see through the abbreviation. Prefer `let` for local abbreviations you don't need to refer to by name.
2. **`⟪a, b⟫_ℝ` for real numbers.** `RCLike.inner_apply` reduces real inner product to multiplication, but in the **opposite order**: `⟪a, b⟫_ℝ = b * a`. Use `simp [RCLike.inner_apply, mul_comm]` if you want `a * b`.
   - **But when both `a b : ℝ`**, `rw [RCLike.inner_apply]` / `rw [EuclideanSpace.inner_eq_star_dotProduct]` often **fail to match** (the inner instance at ℝ × ℝ reduces through a path that doesn't expose the `inner 𝕜 x y` pattern syntactically). Use `change a * b = b * a; ring` — the equality holds by **defeq** so `change` succeeds and `ring` closes.
   - Two scoped notations for the real inner: plain `⟪x, y⟫` from `open scoped RealInnerProductSpace` vs subscript-ed `⟪x, y⟫_ℝ` from `open scoped InnerProductSpace`. They unfold to the same `inner ℝ x y` but are *different notation* — pick one per file and stick with it to avoid "unexpected identifier `_ℝ`" when parsing.
3. **`MemLp.integrable_sq` requires importing `Mathlib.MeasureTheory.Function.L2Space`.** Without it, dot notation fails because Lean unfolds `MemLp` to `And` and looks for `And.integrable_sq`.
4. **`MemLp.integrable_mul` exists** (Hölder for L²×L² → L¹). Use via `hf.integrable_mul hg`.
5. **`Real.sqrt_add_le_sqrt_add_sqrt` does not exist.** Prove inline using `(√a + √b)² = a + b + 2√a·√b ≥ a + b`.
6. **Asymptotic notation `=o[]`.** Use `IsLittleO.comp_tendsto` to specialise along a direction. Use `isLittleO_iff` to extract `∀ c > 0, ∀ᶠ x, ‖f x‖ ≤ c · ‖g x‖` for ε-δ work.
7. **`(𝓝[≠] x).NeBot` for normed fields** is auto-instance from `Mathlib.Analysis.Normed.Field.Basic`. No need to invoke explicitly.
8. **`rw [h]` at `(a-b)²` is too aggressive** when `h : a = b + c`: it rewrites all occurrences of `a`, including ones inside `b`. Use `calc` or `nth_rewrite`.
9. **`omit [...] in` only applies to the next declaration** and must come *before* a docstring `/-- ... -/`.
10. **`field_simp` sometimes closes the whole goal**, after which a trailing `; ring` raises "no goals" — drop the `ring`.
11. **`Measure.map_map hf hg : (μ.map f).map g = μ.map (g ∘ f)` — direction is easy to flip.** Forward (no `←`) *collapses* a double map into a single composed map; `← Measure.map_map` *splits* a `μ.map (g ∘ f)` into two maps. Read the goal carefully before choosing.
12. **`Measure.prod_apply` / `Measure.compProd_apply` / `lintegral_map` leave un-β-reduced integrands.** After these rewrites the goal often looks like `(fun x => μ (Prod.mk x ⁻¹' ...)) y`, which `rw` won't match against plain `μ (Prod.mk y ⁻¹' ...)`. Use `simp_rw` (β-reduces in the rewrite) or `change` (β-reduces on demand) before the next `rw`.
13. **Kernel integrand measurability for `Measure.ext` on `compProd`:** the key lemma is `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left' hs a : Measurable fun b => η (a, b) (Prod.mk b ⁻¹' s)` (note the `'`; without it, you get a less-general version). Without this you'll loop on "measurable integrand" side-goals from `lintegral_map`.
14. **`Fin.cons x v` has a dependent return type that sometimes doesn't propagate.** Inside `refine ⟨fun p => Fin.cons …, …⟩` it resolves from the outer motive. Inside `have h : Measurable (fun U => Fin.cons …) := …`, you often need `(Fin.cons … : Fin (n+1) → ℝ)` as an explicit annotation on the body.
15. **Bridging `e.symm` through `MeasurableEquiv.piFinSuccAbove` to `Fin.cons`:** the chain is `e.symm (x, v) = Fin.insertNth 0 x v = Fin.cons x v`. Mathlib gives you `MeasurableEquiv.piFinSuccAbove_symm_apply` + `Fin.insertNthEquiv_zero` + `Equiv.coe_fn_mk` + `Fin.consEquiv`. Closing the defeq in one go: `simp only [Function.comp, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero, Equiv.coe_fn_mk, Fin.consEquiv]`.
16. **`Kernel.IsMarkovKernel.map` lives in the `ProbabilityTheory.Kernel` namespace** (not `ProbabilityTheory.IsMarkovKernel.map`). Call it as `Kernel.IsMarkovKernel.map κ hf` when `open ProbabilityTheory` is in scope.
17. **`show` vs `change`:** current Mathlib lint forbids `show` when it actually changes the goal; use `change` instead. `show` is only for readability when the stated goal is syntactically identical to the current one.

## 8. Mathlib idioms we reach for

Non-obvious combinations and recipes. Single lemma names that `loogle.sh` or `check.sh` can find on their own are intentionally left out — this section is for patterns the tools can't recover.

* **Translate L² inner product to integral.** `MeasureTheory.L2.inner_def` rewrites `⟪F, G⟫` as `∫ ⟪F x, G x⟫ ∂μ`; then `RCLike.inner_apply` + `mul_comm` reduces pointwise inner to multiplication in the right order (see §7.2 for the flip).
* **Pointwise real inequality default closer.** `nlinarith` with `sq_nonneg` hints, e.g. `nlinarith [sq_nonneg (a - b), sq_nonneg a]`. Closes almost any `a + b ≤ 2c²` style goal where some perfect-square inequality is the trick.
* **Squeeze with eventually-bounded envelopes.** `tendsto_of_tendsto_of_tendsto_of_le_of_le'` takes lower and upper `Tendsto` + `≤ᶠ` inequalities on the thing in the middle. Works over `ENNReal`; use `Eventually.of_forall (fun _ => zero_le _)` for the trivial lower bound.
* **Asymptotic `=o[]`.** `isLittleO_iff` extracts the ε-δ form `∀ c > 0, ∀ᶠ x, ‖f x‖ ≤ c · ‖g x‖`. `IsLittleO.comp_tendsto` specialises a little-o relation along a direction or parameter curve.
* **Abstract Cauchy–Schwarz.** `real_inner_mul_inner_self_le x y` gives `⟪x, y⟫ * ⟪x, y⟫ ≤ ⟪x, x⟫ * ⟪y, y⟫` in any real inner product space — use it to lift `Lp ℝ 2 μ` arguments to the underlying integral form.
* **Convergence in measure, normed target.** `tendstoInMeasure_iff_norm` unfolds the `edist` form of `TendstoInMeasure` to `‖f i x - g x‖`. Pair with `Metric.tendsto_atTop` on the mean to extract an "eventually within δ" statement for an ε-δ split.
* **Lift a real Tendsto to `ℝ≥0∞`.** `(ENNReal.continuous_ofReal.tendsto 0).comp h` turns `Tendsto f atTop (𝓝 (0 : ℝ))` into `Tendsto (ENNReal.ofReal ∘ f) atTop (𝓝 (0 : ℝ≥0∞))`. Standard move when the measure side is `ℝ≥0∞` but the analytic bound is real.

## 9. What *not* to do

* Don't push to the GitHub `origin` without explicit user request. (Pushing to the `cannon` cluster remote is part of the build loop — routine; see §10.)
* Don't change `.gitignore` without flagging it.
* Don't add hypotheses to a finished lemma casually. Existing hypothesis sets have been minimised intentionally; adding more should be justified by a derivation gap.
* Don't **launder unproven content through hypothesis arguments**. If an assumption is mathematically determined by the setup parameters (not a free-choice input), refactor it into a named `sorry`'d theorem or derive it in the proof body. See [notes/hypothesis-discipline.md](notes/hypothesis-discipline.md) for the six-check audit, worked examples, and the constitutive-vs-regularity test for structure fields.
* Don't `axiom` or `admit` anything. Use `sorry` for genuine TODOs and lift them to named lemmas if non-trivial.

## 10. Cluster workflow (FAS-RC) — builds and proof subagents

This laptop cannot run `lake build`. All builds and proof verification run on FAS-RC via the `lean-on-fasrc` skill (`~/.claude/skills/lean-on-fasrc/`); validated branches are pulled back and merged here. **Never run `lake` locally; never `lake update` anywhere.**

* **Build:** `lean-fasrc-build [Module.Target]` (defaults: 'partition = hsph, shared, sapphire, serial_requeue', 4 cpus, 24G, 4h; full-library build needs `LEAN_FASRC_TIME=0-03:00`). Smoke target: `StatLean.AsymptoticStatistics.Core.Hilbert`. Full target: omit (default = lib `StatLean`).
* **Proof subagents:** `LEAN_FASRC_CLAUDE_SRUN=1 lean-fasrc-cluster-claude --branch <area>/<topic> --prompt-file .claude/prompts/<topic>.md`. `SRUN=1` is mandatory (login-node builds get cgroup-killed). Prompt templates live in `.claude/prompts/`.
* **Branches:** `<area>/<topic>` kebab-case (`conc/subgaussian-defs`, `hds/lasso-rate`, `reorg/…`). Never `main`.
* **Protocol per work item:**
  1. *Frame* (laptop): pick the sub-lemma cluster from `notes/<area>/<milestone>/status.md`; declare its **touch-set** (files it may modify/create).
  2. *Stubs* (laptop): write statement-first stubs — precise statements, `sorry` bodies, §2 tags, docstrings — and commit on `<area>/<topic>`.
  3. *Stub gate* (cluster): `lean-fasrc-build --worktree <branch> <Target>` until green-with-sorries. Never hand a subagent non-compiling statements.
  4. *Proof closure* (cluster): the `lean-fasrc-cluster-claude` call above.
  5. *Verification gate* (laptop — subagent self-reports are NOT trusted): `lean-fasrc-fetch` → a **fresh** `lean-fasrc-build --worktree <branch> <Target>` of the branch tip → sorry inventory vs the expected named debts → `git diff main...cannon/<branch>` review (tags present, no hypothesis laundering per the six-check audit, diff ⊆ touch-set, no changes to `lean-toolchain`/`lakefile.lean`/`lake-manifest.json`/the area umbrellas).
  6. *Merge* (laptop): `git merge --no-ff cannon/<branch>` → laptop adds the new modules to the area umbrella → `lean-fasrc-sync` → `lean-fasrc-worktree-rm <branch>`.
* **Laptop-only surfaces** (subagents are prompt-forbidden to touch): `*/Defs.lean` (shared data models), the area umbrellas `StatLean/<Area>.lean`, `StatLean.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `notes/`. The laptop session serializes any change to these.
* **Concurrency:** max 2 concurrent subagent sessions to start; touch-sets must be pairwise file-disjoint (the laptop session is the scheduler).
* **Push to GitHub `origin`** only on explicit user request, typically after a full green build on `main`.

