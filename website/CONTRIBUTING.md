# Contributing to the Stat-Lean website

How to add or revise results on the site. `README.md` describes what the site
*is* and how it is wired; this file is the standard a pull request is held to.

The rules below are the ones that were learned the expensive way — each one
corresponds to a defect that shipped and had to be repaired later. Where a rule
looks fussy, the "why" line says what went wrong without it.

**Golden rule.** A reader lands on one result page, cold, from a search engine.
They have no book, no other tab, and no memory of the previous page. Everything
they need to understand the statement must be on that page.

---

## 0. Before you start

```bash
cd website
npm install
npm run validate:data   # the full data contract; run it early and often
npm run build           # validate + type-check + production build
npm run dev             # http://localhost:5173/website/
```

`validate:data` reads `../StatLean/**.lean`, so run it from a full repository
checkout, not a sparse one. It is the first step of `npm run build`, so a PR
that fails it cannot deploy.

Write JSON with real Unicode and stable formatting, or every PR will show
spurious diffs:

```python
json.dump(data, open(path, "w"), ensure_ascii=False, indent=2)
open(path, "a").write("\n")     # keep the trailing newline
```

---

## 1. The result page

Each entry in `src/data/results.json` renders one page: the informal statement
on the left, the Lean signature on the right, hypothesis chips linking the two,
then the formalization note and the reference block.

### 1.1 Required and optional fields

Required: `id`, `category`, `kind`, `leanName`, `fullName`, `title`, `citation`,
`file`, `docGenUrl`, `informal`, `summary`, `leanSignature`, `hypotheses`,
`hasGraph`. Optional: `formalizationNotes`, `shortRef`, `reference`, `keywords`,
`crossListed`.

Anything else is rejected — the validator uses an exact key set, so a typo in a
field name fails the build rather than silently doing nothing.

Three fields are derived, not authored:

| Field | Must be |
|---|---|
| `file` | normalized repo-relative `StatLean/….lean` path that **exists** and actually declares `leanName` |
| `docGenUrl` | exactly `../docs/<file without .lean>.html#<fullName>` |
| `fullName` | unique across all results; a valid dotted Lean name |

**Why:** `leanName` is checked against the Lean source with comments stripped,
so a page can never claim a declaration that was renamed or deleted.

### 1.2 Informal statement — the core rules

The `informal` field is prose plus KaTeX (`$…$`, `$$…$$`), with
`<span data-link="hN">` anchors marking the phrases that correspond to Lean
hypotheses.

**(a) Self-contained.** Never defer to something the reader cannot see.

> ✗ "Assume the conditions of the Bernstein–von Mises theorem."
> ✓ "Assume a differentiable-in-quadratic-mean model, a prior with a positive
> continuous density near $\theta_0$, and consistent tests separating $\theta_0$
> (the conditions of the
> `<a href="#/result/bernstein_von_mises">Bernstein–von Mises theorem</a>`)."

Link **and** summarise. A link alone still forces a round trip; a summary alone
is acceptable only when the target has no page on the site.

**(b) No bare numbers as content.** A theorem or equation number names a
statement, it does not state one.

> ✗ "…is asymptotically linear with bias term satisfying (25.59), where (25.52)
> is not assumed."
> ✓ "…is asymptotically linear with influence function $\tilde\ell/\tilde I$ up
> to an additive bias term $\mathrm{bias}_n$, which is not assumed to vanish."

A number may follow the content as a parenthetical pointer, never replace it.

**(c) No leading bold restating the title.** The title is already printed
directly above the statement.

> ✗ "**Doob's theorem.** Let $\Theta$ be a Polish space…"
> ✓ "Let $\Theta$ be a Polish space…"

**In fact, do not use bold in the informal statement at all.** The page's
emphasis is carried by the title, the hypothesis chips, and the math itself;
bold inside the statement competes with all three and is never the clearest
tool for the job.

**(d) No vague back-references.** "as above", "the same conditions", "in the
setting of the previous result" — state them. There is no "above" when the page
is reached directly.

**(e) No Lean syntax.** No `∀ x,`, no `fun`, no `↑`, no `Measure`, no Lean
identifiers. Translate to standard mathematical notation or to words. This is
the whole point of the left-hand pane.

**(f) Neutral register for adjustments.** Where the formalization departs from
the printed statement, describe *what we state* and *what we changed*, never
that a source is wrong.

> ✗ "The textbook statement is false as printed; the constant is incorrect."
> ✓ "We adjust the statement by strengthening the constant from $c$ to $2c$,
> which is what the argument supports."

**Why:** these are published, peer-reviewed texts, and a formalization that
needs an extra hypothesis is usually resolving an ambiguity rather than catching
an error. The neutral phrasing is also more informative — it says what we did.

**(g) Math must parse.** Every `$…$` and `$$…$$` is run through KaTeX at build
time, and an unbalanced `$` fails the build.

### 1.3 Hypothesis chips

Each entry of `hypotheses` is `{ id, leanToken, label, note? }`.

* **`label`** — 1–4 words naming the mathematical condition: "monotone
  likelihood ratio", "finite fourth moment". Not provenance, not bookkeeping.
  ✗ "bundled bias-residual assumptions".
* **`note`** — one sentence stating the condition mathematically and
  self-containedly. Never where it came from or what was dropped.
* **`leanToken`** — a substring of `leanSignature`. Tokens are allocated in
  order, each claiming the first occurrence not already claimed, so a token that
  is a prefix of an earlier one will be reported as shadowed.

Two invariants the validator enforces in **both** directions:

1. Every `data-link="ID"` in `informal` names a real hypothesis id.
2. Every id appears **exactly once** — not zero times, not twice.

**Why:** the second direction was missing once, and eight results shipped with
orphaned chips that highlighted nothing on hover.

`label` and `note` are rendered as math, so `$…$` works in them — and must
balance. **Why:** 152 chips once shipped displaying raw `$\sigma$` as literal
text, because the fields were being interpolated as plain strings.

### 1.4 Formalization notes

`formalizationNotes` is where the Lean-versus-book relationship goes: typeclass
choices, why a hypothesis is stronger or weaker, degenerate-input conventions,
constants that differ from the printed ones.

This is the one field where theorem and equation numbers are welcome — they are
legitimate provenance here, not a substitute for content. The prohibition in
§1.2(b) is about the *statement*, which must stand alone.

Adjustments follow the neutral register of §1.2(f).

### 1.5 The reference block

`reference` is `{ formal, pointer, keys, biblio? }`.

* **`formal`** — the full citation of the primary source.
* **`pointer`** — where in that source. See §3 for the numbering rules; get this
  wrong and the reference page files the result under the wrong chapter.
* **`keys`** — reference keys, **primary first**. Every key must exist in
  `references.json`. The first key decides which book's chapter list the result
  appears under.
* **`biblio`** — the bibliographic-comments paragraph: the primary literature
  the result descends from, drawn from the book's end-of-chapter notes.

**The Reference block is the only place the source appears.** The Informal
statement card deliberately carries no citation tag. A statement that has to be
read against a citation is not self-contained (§1.2), and a source printed twice
on one page is just noise — so state the mathematics in the card and let the
Reference block below carry the provenance.

**The bibliographic comment must not name the primary reference again.** The
citation and pointer directly above it already say "van der Vaart, *Asymptotic
Statistics*, Theorem 5.7". Repeating it in the paragraph below is noise, and it
crowds out the original sources that the paragraph exists to record.

> ✗ "…The well-separated-maximum formulation used here is van der Vaart's
> Theorem 5.7, following the empirical-process treatment of van der Vaart and
> Wellner (1996)."
> ✓ "…The well-separated-maximum formulation follows the empirical-process
> treatment of A. W. van der Vaart and J. A. Wellner, *Weak Convergence and
> Empirical Processes*, Springer, 1996."

Point the paragraph *outward*, to Wald (1949), Huber (1967), Pearson (1894) —
the papers a reader would go to next. Every work named in `biblio` should also
appear in `keys` so it is linked inline when author matching succeeds, listed
explicitly under **Cited works**, and present on the References page.

> **Known backlog:** 113 of 432 bibliographic paragraphs currently re-name their
> own primary textbook (vdV 40, Lehmann–Romano 27, Wainwright 22,
> Lehmann–Casella 13, Candès 6, Tsybakov 3, Vershynin 2). New and revised
> entries must follow the rule; touching a nearby entry is a good moment to fix
> one.

---

## 2. Dependency graphs

Graphs are **generated, never authored**. One file per result with
`hasGraph: true`, at `src/data/graphs/<id>.json`.

```bash
# on the cluster, from the repository root (this laptop cannot `lake build`)
lake build
lake exe deps
cd website
npm run layout
```

`lake exe deps` reads `website/targets.txt`, resolves each name against the
built environment, and writes the graphs. It fails on a name that does not
exist, which is what makes the graphs trustworthy.

Three things must stay in lockstep, and the validator checks all three:

1. `targets.txt` has exactly one `<id>\t<fullName>` row per `hasGraph: true`
   result, **in the same order as `results.json`**.
2. `src/data/graphs/` contains exactly those ids, no more and no fewer.
3. Each graph's `root` equals the result's `fullName`, its first node is that
   root, and every node is reachable from it.

Regenerate graphs whenever a result's `fullName` changes, a result gains or
loses `hasGraph`, or the underlying Lean proof changes its dependencies.

Node invariants worth knowing, because the compact global graph relies on them:
`id === full`, `label === full.split(".").at(-1)`, repo nodes come from a
`StatLean` module, Mathlib nodes do not, and Mathlib nodes are always leaves.

`npm run layout` unions the per-result files into two compact assets and
precomputes collision-free positions with the older force-directed recipe.
The StatLean-only graph loads first; Mathlib nodes, their edges and the larger
layout are separate assets fetched only when the visitor enables them. Commit
`global-core.json`, `global-external.json`, `layout-core.json` and
`layout-full.json` whenever the generated per-result graphs change.

> **Performance note for anyone touching `Dependencies.tsx`:** never import all
> files in `src/data/graphs/` into the browser or run fcose there. With 651
> results that means parsing 7.8 MB of repeated data and unioning 4,871 nodes /
> 21,204 edges on the main thread. Keep the centre-seeded, `randomize: false`
> force layout in `scripts/precompute-layout.mjs`; the post-layout separation
> pass is what guarantees rendered nodes do not overlap.

---

## 3. References

`src/data/references.json` is a flat array of `{ key, sortKey, html }`. `key`
must be URL-safe and unique; `sortKey` is the surname the bibliography sorts on;
`html` is the formatted citation.

A book listed in `TEXTBOOK_KEYS` (`src/lib/bookChapters.ts`) gets a
chapter-ordered table of contents instead of a flat list, so it also needs
chapter titles in `CHAPTER_TITLES` — **transcribed from the book's own table of
contents**, not invented.

### Pointer format — read the book's numbering scheme first

`refIndex.ts:parsePointer` derives the chapter, the sort order, and the printed
label from `pointer`. Books differ, and getting this wrong silently misfiles
results:

| Scheme | Books | Example pointer |
|---|---|---|
| `chapter.item` | van der Vaart, Wainwright, Lu, Tsybakov | `Theorem 3.1` |
| `chapter.section.item` | Lehmann–Romano, Vershynin, Robert | `Theorem 3.2.1` |
| **`section.item`** | **Lehmann–Casella (TPE)** | `Chapter 2, §2.5, Theorem 5.4` |

Lehmann–Casella restarts numbering in every section, so its "Theorem 5.4" is the
fourth result of Chapter 2's *fifth section* — and Chapter 1 has a different
Theorem 5.4. **43 numbered items in that book appear in more than one chapter.**
The chapter therefore cannot be recovered from the number, and every TPE pointer
must carry an explicit `Chapter N, §C.S` prefix. The page then prints
`§2.5 Thm 5.4` rather than a bare `Thm 5.4`, which would read as an error.

When adding a book, state its scheme in `bookChapters.ts` and check a few
pointers on the rendered reference page before opening the PR.

---

## 4. The index

`keywords` gives each result **1–3** subject-index terms (prefer one; use more
only when the result genuinely sits under several headings). They populate the
alphabetical index at `/index`.

Style, following van der Vaart's back matter:

* Lowercase common nouns; capitalize only proper names — "sufficient statistic",
  "Neyman–Pearson lemma", "convergence in distribution".
* Singular noun phrases. No trailing punctuation, no LaTeX, no markup.
* **Reuse terms.** An index is only useful when the same concept gets the same
  term every time. Search `results.json` for an existing term before coining a
  variant; "concentration inequality" and "concentration bound" as two entries is
  a bug, not a nuance.
* Terms sharing a leading word are grouped and indented automatically
  ("convergence in distribution" / "convergence in probability" file under a
  single "convergence" head), so put the shared word first where natural.

The head printed above a group is the longest leading run of words the group
shares, in its original casing — so "Le Cam's first lemma" and "Le Cam's method"
file under "Le Cam's". **Why:** grouping on a lowercased first word once printed
proper names as "bernstein", "gaussian", "le".

---

## 5. Topics

Adding a topic is a cross-cutting change. All seven of these must be updated
together or the site breaks in ways the type-checker will not always catch:

1. `src/lib/types.ts` — add the id to the `CategoryId` union.
2. `src/lib/categories.ts` — `{ id, name, tagline, blurb }`.
3. `scripts/validate-data.mjs` — add the id to the `categories` set.
4. `src/components/TopicIcon.tsx` — a `case` for the new id. There is a
   `default` fallback so a missing icon cannot render blank, but add a real one.
5. `src/index.css` — an accent colour `--c-<short>` in **both** the light and
   dark blocks.
6. `src/lib/graphArea.ts` — `AREA_VAR`, `AREA_LABEL`, `AREAS`, and a `DIR_AREA`
   entry mapping the `StatLean/<Dir>/` directory to the category id. Only the
   first two are `Record<Area, …>` and so type-checked for completeness;
   **`AREAS` and `DIR_AREA` are not**, and omitting an entry there is silent —
   the topic drops out of the graph legend, or its nodes are filed under the
   wrong area. Check both by eye.
7. `README.md` — the category table.

**Keep the home-page cards the same height.** The grid uses `auto-rows-fr` with
`flex h-full flex-col` cards over a `min-h-[14rem]` floor, so heights equalise
per row — but a `blurb` much longer than its neighbours still forces the whole
row taller. The twelve current blurbs run 186–211 characters; stay in that band.

Existing topics: `parametric`, `hypothesistesting`, `pointestimation`,
`semiparametric`, `concentration` (displayed as "Probability Inequalities"),
`highdim`, `multipletesting`, `minimaxity`, `optimization`, `bayesian`,
`nonparametric`, `statisticalmodels`, `probability` (displayed as
"Miscellaneous Results").

### Cross-listing a result under a second topic

Some results belong to two subjects at once — the exponential-family pages are
point estimation *and* a class of statistical models. Give such a result an
optional `crossListed: ["<other-topic>"]`; it then appears on that topic's page
and in its search filter, and its own page prints "also in <Topic>" beside the
breadcrumb.

**Never copy the entry instead.** A duplicate would need a second `id` and a
second `fullName`, and `fullName` must be unique — it is the key that ties a page
to its Lean declaration, its `targets.txt` row and its dependency graph. One
declaration, one page, one graph; `crossListed` only changes where it is listed.
`category` stays the result's home topic and continues to drive its accent
colour, its graph-node colour and its prev/next navigation.

Note that `id` and display `name` are decoupled — renaming a topic on the front
page is a `categories.ts` change only. Do **not** rename the id: it appears in
every result entry and in `DIR_AREA`.

---

## 6. Pull-request checklist

- [ ] `npm run build` passes (this runs `validate:data` first).
- [ ] Every new or revised `informal` is self-contained: no "conditions of X",
      no bare numbers as content, no title-restating opener, no bold, no vague
      back-references, no Lean syntax.
- [ ] Hypothesis `label`s are mathematical, `note`s are one self-contained
      sentence, and each id is linked exactly once from `informal`.
- [ ] `biblio` points outward and does not re-name the primary reference.
- [ ] Pointers match the book's numbering scheme (§3).
- [ ] `keywords` reuse existing terms where they exist.
- [ ] Graphs regenerated with `lake exe deps` if any `fullName`, `hasGraph`, or
      proof dependency changed; `targets.txt` still in `results.json` order.
- [ ] Spot-check the rendered pages — the result page, the topic page, the
      reference page's chapter grouping, and the index entry.

**Do not trust a green build as proof the content is right.** The validator
checks structure, not sense: it cannot tell you that a statement is unreadable
on its own, that a chip says "bundled assumptions", or that a pointer is filed
under the wrong chapter. Open the pages.

---

## 7. Deployment

The site is built and published from
[`StatLean/statlean.github.io`](https://github.com/StatLean/statlean.github.io),
not from this repository. Pushing to `main` here does **not** deploy.

```bash
gh workflow run deploy.yml -R StatLean/statlean.github.io -f rebuild_docs=false
```

`deploy.yml` checks out this repository, rebuilds the website, and reuses the
cached doc-gen4 output. It rebuilds the Lean docs only when the Lean sources
changed or `rebuild_docs=true`, so a website-only change deploys in ~1 minute
instead of the ~3 hours a full doc-gen4 build takes. Pass `rebuild_docs=true`
after Lean changes that should appear in `/docs/`.

Verify afterwards that both `/website/` and `/docs/` return 200 — the deploy
uploads a single Pages artifact containing both, so a docs cache miss would
publish an empty `/docs/`.
