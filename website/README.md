# Stat-Lean — the interactive website

A React + Vite + Tailwind front-end that aligns informal mathematical statements
with their Lean 4 / Mathlib formalizations, organized across four categories of
asymptotic statistical theory. Deployed to GitHub Pages at
`https://junwei-lu.github.io/Lean-Asymptotic-Statistical-Theory/website/`.

## Develop

```bash
cd website
npm install
npm run dev        # http://localhost:5173/Lean-Asymptotic-Statistical-Theory/website/
npm run build      # type-check + production build into dist/
```

## How it works

The site is driven by two data layers:

1. **`src/data/results.json`** — authored content. One entry per result
   (informal statement with `$…$` KaTeX math and `<span data-link="hN">` hover
   anchors, the exact Lean statement signature, the hypothesis ↔ informal-text
   correspondence, citation, and doc-gen4 URL). The schema is in
   `src/lib/types.ts`.

2. **`src/data/graphs/<id>.json`** — generated dependency graphs. Produced by
   the Lean executable `Scripts/ExtractDeps.lean`:

   ```bash
   # from the repository root, after `lake build`
   lake exe deps
   ```

   For each target it walks the declaration's statement/proof dependencies
   *through repository lemmas*, stopping at the first Mathlib (or core)
   declaration, and emits a `{ root, nodes, edges }` graph. Nodes are
   colour-coded (this result / repository lemma / Mathlib leaf); Mathlib leaves
   link to the Mathlib docs. The targets list is `website/targets.txt`
   (`<id>\t<fullName>` per line), regenerated from `results.json`.

## Categories

Results are organized into four categories (defined in `src/lib/categories.ts`):

| Category | `id` | Content |
|---|---|---|
| Parametric Statistics | `parametric` | Local asymptotic normality, DQM, LAN expansion, Hájek–Le Cam bounds |
| Semiparametric Statistics | `semiparametric` | Tangent spaces, efficient influence functions, score operators |
| Empirical Processes | `empirical` | Glivenko–Cantelli, Donsker, bracketing entropy, maximal inequalities |
| Miscellaneous Results | `probability` | Prékopa–Leindler, Anderson's lemma, Le Cam lemmas, multivariate CLT |

## Key features

- **Side-by-side panes** — informal statement (left) vs. Lean code (right).
- **Bidirectional hover-linking** — hovering a Lean hypothesis highlights the
  corresponding informal phrase and the legend entry, and vice-versa
  (`src/pages/ResultDetail.tsx`, driven by `data-link` ids).
- **Note on informalization** — each result has a dedicated note box explaining
  design choices, typeclass decisions, and how the Lean encoding relates to the
  textbook statement.
- **Dependency graphs** — Cytoscape + fcose, lazy-loaded on demand.
- **doc-gen4 + source links** per result, pointing to
  `https://junwei-lu.github.io/Lean-Asymptotic-Statistical-Theory/docs/`.
- **Team page** — linked from the top navigation bar.
- Light / dark dual theme (defaults to light) with a per-category accent system.

## Deployment

`.github/workflows/docs.yml` builds the doc-gen4 API docs (only when Lean
sources change), runs `lake exe deps`, builds this site, and serves everything
under one GitHub Pages artifact:
`…/` (landing) · `…/docs/` (API) · `…/website/` (this site).

Website-only pushes skip the 45-minute Lean build entirely.
