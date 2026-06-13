# Workflow — human/AI collaboration process

> This document records the project's **process** (how we do things), and complements [CLAUDE.md](../CLAUDE.md) which carries the **principles and conventions** (why we do things):
> - CLAUDE.md: why we work this way, Lean-level rules, Mathlib toolkit.
> - workflow.md: **how** we work, what each step looks like, what it delivers, when to switch sessions / models.
>
> This file only describes practice that has stabilised. **Unsettled pieces are intentionally left blank** — better to wait for the pattern to show up two or three times than to codify too early.
> LeanBlueprint migration is a placeholder entry (see §4.4), to be fleshed out into its own doc once Thm 7.2 is closed.

---

## 1. Top-level invariants

The process-layer hard constraints are just three; everything below fleshes them out:

1. **Statement-first, proof-second.** Before proving a sub-lemma, its full statement must be written down and must plug into context (see §2.2).
2. **Every `sorry` corresponds to a named lemma.** Never `sorry` an anonymous `have` inside a big proof — the gap then disappears from `lake build 2>&1 | grep sorry`.
3. **Before introducing a hypothesis, ask: can this be derived?** A hypothesis is an IOU on a proof; the hypothesis-discipline loop (see CLAUDE.md §2) is about steadily squeezing these. **When a hypothesis cannot be immediately derived, record a one-line *discharge plan* next to the introduction site** — "automatic in finite-dim via `dqm_fisher_integrable` per coordinate + Cauchy–Schwarz", "Step-N corollary (see outline.md)", "external per vdV §7.2 p. NN", etc. An undocumented IOU tends to become invisible across sessions, and then someone else has to re-derive whether it can be discharged at all.

---

## 2. Standard workflow for entering a theorem

### 2.1 Mathematical preparation and dependency analysis

This step is where the whole collaboration starts. Skipping it makes every subsequent conversation drift.

**Input**: a target theorem from the area's reference text (vdV for AsymptoticStatistics, Lu *Big Data Analysis* for ConcentrationInequalities / HighDimensionalStatistics, or another source).

**Steps**:
1. Read the source proof; write an informal outline in `notes/<area>/<milestone>/outline.md` (any language, formulas welcome, no Lean syntax required).
2. Enumerate **every concept** the proof uses, tagged: `already in Mathlib` / `already in our library` / `needs building`.
3. Enumerate **every lemma** the proof uses, tagged the same way.
4. In the outline or status doc, record sub-lemma dependencies as a table or bullet list — no formal diagram required; a "lemma name → its direct dependencies" table is the DAG equivalent.
5. Identify "one-liner in the book, explicit work in Lean" steps — these are the gaps that most often slip.

**Deliverable**: `notes/theorem_X_Y/outline.md`, containing:
- the informal proof outline,
- the dependency DAG,
- the "needs building" list (infrastructure gaps),
- identified implicit hypotheses / Lean-specific pitfalls.

---

### 2.2 Decompose and write Lean statements first

**Steps**:
1. Pick a decomposition — if the source proof has numbered steps, reuse them; otherwise cut along natural semantic boundaries.
2. For each sub-lemma, write the precise Lean statement: signature + conclusion + `:= by sorry`.
3. With those sub-lemma stubs, wire up the **main theorem assembly** — the whole file is statements + `sorry` at this point, but `lake build` should pass.
4. Commit this "scaffold" before filling in any proof.

**Check**:
- Do the sub-lemma signatures compose into the main theorem? (If not, the decomposition is wrong.)
- Does each sub-lemma stand on its own, potentially reusable by a neighbouring theorem?
- Is the hypothesis set minimal? (Every hypothesis must be justifiably necessary in the CLAUDE.md §7 sense.)

---

### 2.3 Pre-decide shared data models (smoke-test first)

**When to apply**: whenever two or more sub-lemmas will share the same data / index structure — typically a sample (`ℕ → Ω → 𝓧` vs. `Fin n → Ω → 𝓧`), a triangular-array encoding, a filtration, a kernel. If only one sub-lemma touches the object, skip this step.

**Why**: the encoding choice rarely changes *whether* a statement is provable, but it strongly affects *which Mathlib lemmas fit without adapter work*, and — more subtly — whether cross-parameter statements can even be **written down cleanly**. A per-`n` encoding (`Fin n → Ω → 𝓧`) is fine for single-`n` claims but makes cross-`n` claims (e.g. `max_{i ≤ n} |W_{n,i}| → 0` in probability, which requires all `M_n` to live on one space) syntactically awkward; Mathlib's i.i.d. / LLN infrastructure is mostly stated on `ℕ → Ω → 𝓧`. Picking first, writing N sub-lemma signatures, then discovering the n-th signature needs a different encoding forces mass signature rewrites plus all downstream assembly.

**Steps**:
1. List the candidate encodings (≥ 2; don't commit prematurely).
2. Identify the **sub-lemma that most stresses the encoding** — usually the one requiring cross-parameter coordination (cross-`n` convergence, max / sup across the array, filtration compatibility), or the one that leans hardest on a specific Mathlib API.
3. Under each candidate, sketch that sub-lemma's signature and search Mathlib (`loogle.sh` + `check.sh`) for the main lemmas it will cite. If the interface clicks without adapter contortions, the encoding survives; otherwise try the next candidate.
4. Commit the chosen encoding as a short note in the theorem's `outline.md` (or a separate `design_notes.md`): one paragraph per candidate considered, plus a one-sentence rationale for the one chosen.

**Budget**: 30–60 min total. If no candidate clears the smoke-test at the boundary, **stop and escalate** — the obstacle is usually a missing piece of infrastructure (an adapter lemma, a new structure), which wants its own `ForMathlib/` file rather than being papered over inside the target theorem.

**Deliverable**: a short design-rationale block committed alongside the outline, plus the smoke-test sub-lemma written out (and ideally proved; `sorry` is acceptable once the encoding is clearly fine and the remaining proof is routine). After this, §2.4's batch statement-writing can proceed knowing the signatures won't unwind.

---

### 2.4 Conventions for delegating to Claude

When asking Claude to prove a lemma, use the prompt template below. Skipping any of its pieces tends to cause rework.

```
Target lemma: <lemma name or informal statement>

Available tools:
  - Already proved: <list>
  - Mathlib: <expected lemma names; if unsure, search shapes with
              tools/loogle.sh and verify signatures with
              tools/check.sh — full decision table in tools/search.md>

Mathematical idea (one or two sentences):
  1. ...
  2. ...

Caveats:
  - <type conversions / edge cases / known traps>

Requirement: follow "three things before code" — before writing tactics, say
  (a) what this lemma states mathematically
  (b) why it's true
  (c) which Mathlib lemmas you expect to use (ideally with at least one
      verified on the spot via check.sh; otherwise at least name the shape)
then start writing tactics.
```

**"Three things before code" is a hard rule**: without forcing Claude to say those three things, its first-pass tactics tend to drift (wrong level of abstraction, sledgehammers on trivial goals). Aligning upfront costs less than the rework it prevents.

---

### 2.5 Time-boxing and trade-off communication

The process-layer concretisation of CLAUDE.md §6. Every time Claude is sent after a subtask of **unknown cost** (Mathlib API search, unfamiliar tactic, a type-conversion that smells risky), the prompt — or the very first exchange — must specify:

- **Budget**: e.g. "try shape-searching with `loogle.sh` plus a couple of `check.sh` verifications; if inconclusive after 5 minutes, stop and report". At the boundary, stop — don't silently keep digging.
- **Alternative plans**: when a step has a "fast but rough" vs. "slow but clean" choice, Claude must report both and their costs, not silently pick.

**Why it's a hard rule**: Lean rabbit holes routinely look like 10-minute tasks and turn into 90-minute ones. Agreeing on a budget costs nearly nothing and saves a lot of sunk time.

---

### 2.6 In-flight assessment — extract reusable theorems when they surface

**When to trigger**: either (a) mid-proof, a sub-argument is clearly a reusable theorem-agnostic fact, or (b) the proof has overshot its budget by ~2× without a clear end in sight. Either signal = **stop and assess**; neither signal by itself = **finish**.

**Assessment content** — describe the state:
1. Current progress and what remains.
2. What's blocking closure (missing Mathlib lemma / new hypothesis obligation / design issue).
3. **Is there a reusable theorem hiding in the work so far?** Natural cut points:
   - A theorem-agnostic fact that belongs in `ForMathlib/*` or a concept directory.
   - An intermediate identity or bound that stands alone.
   - A specific obligation wanting to be a named lemma or hypothesis.
4. Recommendation: press on / split into K pieces / commit partial + defer / roll back and redesign.

**The goal is extracting value, not decomposition for its own sake.** A 200-line proof that's making linear progress and whose pieces are all glue should be finished, not chopped into thin helpers. Splitting for length alone adds boilerplate (imports, signatures, docstrings) without value.

**When NOT to split**:
- Proof is making visible linear progress, just long.
- No theorem-agnostic core surfaces; pieces are single-use glue.
- Estimated remaining work < 1/3 of work already done.

**What this rule catches** (dual-sided):
- the sunk-cost case — a multi-hour proof pushed through in one go, failing near the end, with nothing commit-worthy;
- the missed-infrastructure case — a 30-line fragment deep in a proof that would be a useful reusable lemma, but was left buried inside a chapter file because no one paused to look.

**Worked example**: Thm 7.2 Step 2 (commit `c731e9e`) was split into three reusable cores (`dqm_residual_rate_along` etc.) once assessed at 2× budget; Step 3 (commit `d0b0843`) then closed in ~1 h reusing them.

---

## 3. Review chain (in-session only)

This document collects **in-session** review practices only. The entry point for cross-session / cross-model review is [AGENTS.md](../AGENTS.md) — that's the doc written for external AI agents (Codex / Cursor / Gemini …) brought in for a final audit pass.

### 3.1 First-pass self-review

After Claude delivers a lemma or a batch of changes, walk this checklist. The focus is **completeness and boundaries**, not chasing every tactic detail.

**Checklist**:
- [ ] Are all the propositions you asked for actually formalised? (Cross-check against the original prompt; don't miss a clause.)
- [ ] Were any out-of-scope hypotheses added? If so, can they be derived away using the §1 hypothesis discipline?
- [ ] Does every `sorry` correspond to a **named** sub-lemma, not a hidden `have`?
- [ ] Does `lake build` pass? Do warnings narrow down to `sorry` notices only — no stray `unused variable` / `unused import`?
- [ ] Do the new lemma signatures still plug into the upper assembly? (Types, implicit arguments, `variable` blocks — has anything drifted?)
- [ ] Is there any fragment that could be **promoted** to the infrastructure layer? (See §4.3 core / assembly.)

**Pass condition**: every item above passes. If any fails, **fix it in the current session** — don't accumulate.

---

### 3.2 Probing alignment (when disagreement surfaces)

When the checklist catches something, or you're unsure about the direction of Claude's proof, don't edit the code directly — probe first to surface the disagreement:

- "Why did you use X instead of Y?"
- "Where does that hypothesis come from? Can it be eliminated?"
- "In this `simp only [...]` step, which lemma is doing the real work?"

**Key principle**: ask Claude to **explain** rather than to **rewrite**. The drift exposed in the explanation is usually more diagnostic than any replacement code — if the explanation is sound, accept; if not, then ask for a rewrite.

---

### 3.3 Step-level audit on request

Beyond §3.1's delivery-time checklist, the collaborator may at any point request a status audit on one or more already-closed steps. The response must, per step:

1. **Real vs sorry** — does `lake build 2>&1 | grep sorry` flag this lemma?
2. **Hypothesis classification** — for each hypothesis, classify as:
   - *external* — a standard assumption the theorem genuinely requires (the hypothesis is part of the theorem's contract, not an IOU);
   - *derivable (pending)* — can be discharged from more primitive hypotheses already in the project; *state when/how* this discharge will happen;
   - *discharged* — pointer to the lemma that proves it (e.g. `dqm_fisher_integrable`).
3. **Deferred assembly obligations** — anything waiting for downstream steps (e.g. i.i.d. sample encoding, a Step-N corollary that wasn't available at the time of closure).

**Why this is a separate review mode**: as a project matures, hypotheses that were *derivable (pending)* become *derivable (now)* whenever the step that discharges them closes. It is **not automatic** that this newly-unlocked discharge gets wired — the §3.1 self-review only runs at delivery time. Without periodic §3.3 audits, IOUs accumulate silently.

**Worked example**: after Thm 7.2 Step 3 closed (commit `d0b0843`), Step 6b's `h_delta_integrable` / `h_delta_l1` flipped from *pending* to *dischargeable*, but noticing this required an explicit audit pass.

---

## 4. Commits and maintenance

### 4.1 Commit granularity

- **One real proof = one commit**.
- **One refactor = one commit**.
- **Do not mix a real proof with a refactor** — `git blame` later won't tell you whether the proof was broken or the refactor was.
- Commit message: **plain imperative, no prefix**, matching the current `git log` style (e.g. "Add Step 4 probability core for thm 7.2 LAN expansion", "Close thm 7.2 (i) and (ii) with zero auxiliary hypotheses"). The `/commit` skill auto-detects style from history — do not hard-code a prefix convention here that conflicts with the skill's inference, or the two will drift apart.
- Title describes *what changed*; body explains *why* (only when non-trivial).

### 4.2 When to update CLAUDE.md / the status doc

Maintaining these two docs is cheap; letting them rot is expensive. Update immediately when:

**CLAUDE.md**:
- A Lean trap surfaces (§7 "gotchas").
- A new Mathlib idiom starts getting reused (§8 "idioms we reach for").
- Any project-wide convention changes (file-split rules, commit rules, etc.).

**Status doc** (one per theorem):
- A sub-lemma closes → update the sub-lemma table.
- A hypothesis set changes → update the corresponding row.
- A new sub-task surfaces → add it to "remaining hypotheses" / "next steps".
- A milestone lands → update the header progress summary.

**Anti-pattern**: updating code without updating the status doc. Two or three times through this and the status doc is fully out of sync and useless.

### 4.3 Core / Assembly bookkeeping

**Background**: a step can often be split into two parts that **close at different times** —

- **core**: a theorem-agnostic mathematical fact, placed in a theorem-agnostic file (`ForMathlib/*`, `ParametricFamily/*`, `DQM/*`, …), which can be closed independently and reused by other theorems.
- **assembly**: the wiring that applies the core to this chapter's specific objects (e.g. `W_{n,i}`, `score_mean_zero`, a particular clause of `LAN_expansion`), placed in `Ch7/Theorem7_2.lean`, and which typically cannot close until the surrounding steps of this chapter are in place.

The three-layer directory structure (`ForMathlib/` → concept dirs → `Ch*/`) **structurally enforces** this split: cores only live in the first two layers, assemblies only in `Ch*/`. The directory path is the classification.

**Typical examples**:

| Step | core | assembly |
|---|---|---|
| Thm 7.2 Step 1 | L1–L4 + `score_mean_zero` in `ParametricFamily/Score.lean` | `LAN_expansion` clause (i) in `Ch7/Theorem7_2.lean` (originally owed `h_Fisher` / `h_fminus_memLp`; closed once `DQM/Properties.lean` discharged both) |
| Thm 7.2 Step 4 | `tendstoInMeasure_of_tendsto_mean_of_tendsto_variance` in `ForMathlib/MeanVarConvergence.lean` | `sum_W_decomp` in `Ch7/Theorem7_2.lean` (pending the i.i.d. sample encoding) |

**When to split**:
- The core can be stated without reference to `ParametricFamily`, `DQM`, or a specific `W` definition.
- The assembly needs artefacts from other steps of this chapter (i.i.d. sample, Step 6 output, …) before it can close.
- Trigger signal: "I can prove the general fact today, but wiring it up has to wait for Step X." That's the core / assembly split talking.

**How to record in the status doc**: each split step occupies two rows in the sub-lemma table, named with `-core` / `-assembly` suffixes (or equivalent natural names), each with its own ✅/❌. See the Step 4 entry in [`theorem_7_2/status.md`](theorem_7_2/status.md) for the current pattern.

**When not to split**:
- The step itself is just thin glue — extracting a core leaves 1–2 lines, pure noise.
- The core already exists in Mathlib — don't reinvent; the assembly just calls it.

---

### 4.4 When to migrate to LeanBlueprint (**placeholder**)

**Current status**: not integrated.

**Migration triggers**:
- Thm 7.2 (i)(ii)(iii) all closed.
- Lemma count exceeds ~50 and the hand-maintained status doc becomes unwieldy.
- Preparing to share the project publicly (blueprint's HTML page is a good showcase).

**Work required at migration time** (placeholder; full doc later):
- Tag every existing lemma with `\lean{}`.
- Rewrite the outline into blueprint `\begin{definition}` / `\begin{theorem}` form.
- Set up CI to auto-build the HTML.

**Reference**: Tao's PFR project (github.com/teorth/pfr) is the current gold-standard template.

---

## Appendix: Known gaps in the current process

Things deliberately deferred; fill in on the next iteration:

- [ ] No stabilised prompt template for cross-session / cross-model review yet. For now AGENTS.md carries the role description, but a concrete prompt to paste on top of it hasn't been written.
- [ ] External reviewer agents have limited context windows — a strategy for feeding very large files (beyond manual excerpting) hasn't been decided.
- [ ] Once LeanBlueprint is integrated, it's unclear whether the status doc should remain and at what granularity.
- [ ] When to require Claude to write a `.tex` proof before translating to Lean is decided by intuition — if a reusable rule emerges, write it up separately.
