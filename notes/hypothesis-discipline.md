# Hypothesis Discipline — avoiding hidden strength

> Operational complement to CLAUDE.md §2. Six checks make a main theorem's claim rigorous.
>
> `<ref>` below is the area's reference text: `vdV` for AsymptoticStatistics, `Lu-BDA` for ConcentrationInequalities / HighDimensionalStatistics. Worked examples in this file are drawn from the AsymptoticStatistics (vdV) milestones — the *principles* are area-agnostic.

## Quick checklist (write-time, every commit)

If your commit adds any new `theorem`, `def`, or `structure` field, **all three** are PR gates. Skipping costs ~30 min audit later vs ~5 min now.

- [ ] **Each new `theorem` hypothesis** tagged `-- USER-INPUT: <claim>; <ref> §X.Y` (book input) or `-- LEAN-ONLY: <claim>; <why no scope change>` (Lean-side adapter / typeclass artifact).
- [ ] **Each new `structure` field** has inline docstring `Constitutive (<ref> §X.Y): …` (book demands it) — or, if book allows objects without it (regularity), it's NOT a field but a hypothesis on theorems that need it.
- [ ] **Each new `def`** on a book-facing concept has docstring stating the book concept it formalizes + edge behavior (degenerate-input fallback, e.g. `multivariateGaussian` on non-PSD returning `Measure.dirac μ`).
- [ ] If closing a **main theorem** (not a helper): also run the six-check audit in §"The six-check sufficient condition" below.

The bullet "main theorem" carve-out applies ONLY to the six-check audit (a heavyweight ~10 min review). The three write-time tags above apply to **every** new declaration regardless of whether it's a main theorem or a helper — there is no "ForMathlib helper" exception. Failure mode: confusing "this isn't a main theorem, audit doesn't apply" with "this isn't a main theorem, write-time tags don't apply" — the latter is wrong.

## The problem

Lean's `0 sorry` compile does **not** imply "proven". Unproven content can be
smuggled in through the signature (`(h : P)` where `P` is a theorem we owe, not
a user input), through dependencies (a helper using `sorry` or a custom
`axiom`), or through definitions (a `structure` field / `def` / instance
constraint that silently narrows the book's scope). `#print axioms` and
`grep sorry` catch the middle case but not the others.

## The six-check sufficient condition

A main theorem `main : P` is honestly proven ↔ **all six** pass.

### Mechanical (every build, CI; 0 attention cost)

1. **No stray sorry.** `lake build 2>&1 | grep "uses .sorry"` is either empty or
   matches a documented inventory of known-incomplete leaves.
2. **Clean axioms.** `#print axioms <main>` reports only
   `propext, Classical.choice, Quot.sound`. Anything else (`sorryAx`, custom
   `axiom`) is a failure.

### Main theorem signature, vs book (human, ~10 min per theorem)

3. **Hypothesis list.** Each `(h : P)` in the signature either matches a
   book-stated condition on that theorem, or is explicitly tagged as a
   formalization-specific input (`[DecidableEq ι]`, etc.) with a note on why
   it doesn't narrow scope.
4. **Conclusion.** Lean's conclusion statement is equivalent to the book's, no
   silent weakening (e.g. proving for a subset where the book claims for all).
5. **Instance constraints.** Each `[Foo X]` corresponds to a book assumption
   (implicit or explicit), or is tagged Lean-only with justification.

### Transitive definitions, vs book (human, one-time per def)

6. **Our own `structure`s and `def`s on the signature's transitive dependency**
   (the ones *we* authored — Mathlib is a trusted base) each pass:
   - **Structures**: every field classified as **constitutive** (book's
     concept literally requires it; removing it makes the object not the
     book's `X`) or **regularity** (book allows objects without it). Only
     constitutive fields are legitimate; regularity must be a hypothesis to
     theorems that need it.
   - **Defs**: edge behavior (degenerate-input fallback, e.g.
     `multivariateGaussian` on non-PSD) is documented, and confirmed not to
     change the scope the book intends to cover.

Each audited item is recorded in `notes/audit-log.md` with date + book
reference. Structures/defs are re-audited only when modified.

## What each check catches

| Risk | Caught by |
|---|---|
| `sorry` / `axiom` anywhere in dependencies | (1), (2) — mechanical |
| Hypothesis laundering at *any* level | (3) — follows from Lean's type system: any laundered hypothesis must surface either on `main` or as explicit sorry |
| Conclusion weakened vs book | (4) |
| `[Foo X]` instance pollution | (5) |
| Structure field creep | (6), structure row |
| Definition edge-behavior drift | (6), def row |

The type-system argument for (3) matters: if a helper lemma has a laundered
hypothesis, and `main`'s signature is clean, then either (i) `main` supplies
that hypothesis internally (its construction must itself be sound, recursively),
or (ii) somewhere a `sorry`/`axiom` is invoked (caught by (1)(2)). There is no
third escape — so auditing `main`'s signature + Tier 0 fully covers channels
①②; intermediate lemmas don't need per-lemma auditing.

## Write-time discipline (mandatory at creation, not backfilled)

Checks (3)–(6) are cheap **iff** the book references needed to verify them
already exist. Make them inline at creation time — author knows intent best,
no accumulation of unreviewed definitions.

**Every non-trivial hypothesis on a main theorem** gets a one-line
justification comment:
```lean
(hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
-- USER-INPUT: regularity property of M at θ₀; vdV §7.2 hypothesis of Theorem 7.10.
```
Tag as `USER-INPUT` + book section (or `LEAN-ONLY` + why no scope change).
Writing the tag forces the question "is this really user-input or a laundered
gap?" — many laundering cases are caught here before they land.

**Every `structure` field** we author gets a classification + book citation in
a docstring next to the field:
```lean
structure ParametricFamily (𝓧 Θ : Type*) where
  density : Θ → 𝓧 → ℝ
  /-- Constitutive (vdV §1.X): a parametric family is θ ↦ P_θ where each P_θ
      is a probability measure; unit integral is what makes this so. -/
  density_unit_integral : ∀ θ, ∫ density θ = 1
```

**Every `def`** we author that appears in a book-facing concept gets a
docstring stating the book concept it formalizes + any edge-behavior note:
```lean
/-- Multivariate Gaussian `N(μ, S)` for positive-semidefinite `S` (vdV notation).
    Edge behavior: on non-PSD `S`, returns `Measure.dirac μ`; book never invokes
    this case, so the fallback does not change scope. -/
noncomputable def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) : ...
```

**PR rule.** Any new theorem / structure field / def without these
annotations fails review. No backlog permitted — if the annotation is hard to
write, the hypothesis/field/def is probably wrong (laundering, regularity
masquerading as constitutive, or semantic drift) and should be refactored
before merging.

This turns check (6) from "audit everything against the book, retrospectively"
into "verify existing inline citations" — cost drops from ~30–60 min per
structure to ~5–10 min. Same rigor, a fraction of the attention.

## The constitutive vs regularity test

The subtle part of (6). A field belongs in a structure iff removing it would
make the object **no longer an `X`** in the book's sense.

- `density_unit_integral : ∀ θ, ∫ density θ = 1` in `ParametricFamily` —
  **constitutive**: vdV's "family of probability measures" requires each `P_θ`
  to be a probability, so unit integral is definitional. Legitimate field.
- `density_smooth_in_θ : ContDiff 2 density` in `ParametricFamily` —
  **regularity**: plenty of vdV's valid families aren't C². **Must not** be a
  field; must be a hypothesis to theorems that need it.

Rule: every constitutive field must cite the book definition that demands it.
Without citation, the classification is unverifiable.

## Worked examples (current project)

**`hp_pos` in `LAN_expansion_iii` — dead hypothesis**. Declared in signature,
never used by name in the proof body. Caught by (3): no justification can be
written for why it's needed. Treatment: delete.

**`hpn_pos` in `LAN_expansion_iii` — over-strong**. Declared as full μ-ae
positivity; proof only uses ν_θ₀-ae (on `support(p_θ₀)`). Caught by (3) and
(4): Lean version excludes book-valid families where `p_{θ+tu}` vanishes
outside `support(p_θ₀)`. Treatment: weaken to `ν_θ₀`-ae form (equivalently,
`μ.withDensity p_θ₀ ≪ μ.withDensity p_{θ+tu}` on relevant θ).

**`hLogLik_*` in `LAN_representation` — laundered gap**. Four hypotheses
(`hLogLik_meas`, `hLogLik_is_log_ratio`, `vLog`, `hLogLik_weak`) whose
own source-code comment reads "gap from Step 3's output". Caught by (3):
the "justification" admits it's a gap. Treatment: derive internally from
Step 3 output.

## Trust assumptions (not audited; accepted as foundations)

- Lean 4 kernel soundness.
- Standard axioms `propext, Classical.choice, Quot.sound`.
- Mathlib as a trusted base (its structures/defs are audited upstream).

## Residual risk

Even with all six checks faithfully done, two failure modes remain:

1. **Human error in (3)–(6).** Audits rely on human book comparison; a
   missed field or overlooked hypothesis slips through. Mitigation: second
   reviewer for main theorems; rerun audits on any signature or definition
   change.
2. **Book-interpretation ambiguity.** vdV's prose is informal; some conditions
   have genuine reading ambiguity (e.g. what exactly is "a parametric family"?
   edge cases of non-positive density). Mitigation: in `audit-log.md`, record
   the chosen reading with rationale — not as perfect, but as an explicit,
   reviewable judgment.

Neither can be reduced to zero short of formalizing vdV itself. **Accept this
explicitly** in the status doc rather than claiming infallibility.

## See also

- [CLAUDE.md §2](../CLAUDE.md) — hypothesis discipline bullet
- [CLAUDE.md §9](../CLAUDE.md) — anti-pattern bullet
- [notes/workflow.md](workflow.md) — general session workflow
