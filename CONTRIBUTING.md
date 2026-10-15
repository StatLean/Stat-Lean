# Contributing to Stat-Lean — Statistical Theory in Lean 4

Thank you for your interest in contributing! This project formalizes
statistical theory in Lean 4 / Mathlib, organized into per-area sublibraries
under `StatLean/` — asymptotic (parametric & semiparametric) statistics,
Bayesian statistics, concentration inequalities, high-dimensional statistics,
minimaxity, multiple testing, and optimization. Contributions of new theorems,
improved proofs, website content, and documentation are all welcome.

## Contributor responsibility

Contributors should be responsible for the code they submit, including its
definitions, assumptions, theorem statements, and proofs. They should be
prepared to explain relevant mathematical and implementation choices and
address review feedback. These expectations apply equally to AI-assisted
contributions.

## Getting started

1. Fork the repository and clone your fork.
2. Follow the [Installation Guide](README.md#installation-guide) to set up Lean
   and fetch the Mathlib cache.
3. Run `lake build` to verify that everything compiles before making changes.

## Types of contributions

### New formalizations

If you want to add a new theorem or definition:

- Place Lean source files under `StatLean/` in the appropriate area
  (e.g., `StatLean/Bayesian/`, `StatLean/ConcentrationInequalities/`,
  `StatLean/AsymptoticStatistics/`). Pure-math prerequisites that could live in
  Mathlib go in that area's `ForMathlib/` subdirectory; concept files should
  stay theorem-agnostic, with theorem-specific wiring in assembly files.
- Ensure the new module is imported in its area umbrella
  (`StatLean/<Area>.lean`), which `StatLean.lean` imports.
- Every user-facing result should have a corresponding entry in
  `website/src/data/results.json` with:
  - `informal` — the natural-language statement with LaTeX math (`$…$`)
  - `leanSignature` — the verbatim Lean `theorem`/`def` header
  - `hypotheses` — the list mapping Lean hypothesis names to their
    informal descriptions (used for hover-highlighting)
  - `citation` — the required website citation field; for a sourced result,
    identify the theorem/lemma in the source text. See the
    [website contribution guide](website/CONTRIBUTING.md) for the data format.
    If no published source applies, identify the contributor-provided statement
    or project documentation.

### Improving existing proofs

- Shorter or more readable proofs are always welcome.
- If a proof currently uses `sorry`, replacing it with a complete proof is a
  high-priority contribution.
- Lean proofs should be self-contained: avoid introducing new `sorry`s.

### Website content

The interactive atlas lives in `website/`. See
[`website/README.md`](website/README.md) for the development workflow.

- Informal statement improvements: edit the `informal` field in
  `website/src/data/results.json`. Statements should be in natural language
  with LaTeX math — no Lean-style identifiers.
- Adding a result to the site: add a full entry to `results.json` and a
  corresponding line in `website/targets.txt` (`<id>\t<fullName>`).

### Bug reports and suggestions

Open a [GitHub issue](https://github.com/StatLean/Stat-Lean/issues)
describing the problem or suggestion.

## Pull request guidelines

- **Branch from `main`** — create a feature branch (`git checkout -b my-feature`).
- **One logical change per PR** — keep related Lean code, result pages, and
  documentation together; separate unrelated refactors or website edits.
- **All files must compile** — run `lake build` (and for website changes,
  `npm run build` inside `website/`) before opening a PR.
- **Commit messages** — use a short imperative subject line, e.g.:
  `Add Donsker theorem for VC classes` or `Fix: remove sorry in LANExpansion`.
- **Describe the mathematical content** — provide or link to a clear
  natural-language statement, including relevant definitions, assumptions,
  and conclusions, and explain its intended use. For existing results,
  highlight changes to definitions, assumptions, conclusions, or public
  interfaces. Include references where applicable; claims of correspondence
  with a particular published result should identify its source and location.

## Review process

Contributions are reviewed for mathematical accuracy, clarity, and
maintainability, including whether the Lean formalization matches the stated
mathematical content. Reviewers consider the documented validation results
alongside the code and mathematical statement. Maintainers make the final
acceptance decision. See [Reviewing contributions](REVIEWING.md) for the
review guidelines.

## Code style

### Lean

StatLean follows Mathlib's [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[documentation](https://leanprover-community.github.io/contribute/doc.html) conventions. The
Mathlib linters enabled in `lakefile.lean` check many of them during `lake build`; new code should
not add linter warnings.

Naming:

- Theorems and lemmas are named in `snake_case`.
- `Prop`-valued definitions, types, structures and classes are named in `UpperCamelCase`, for
  example `IsPDonsker`.
- Other definitions are named in `lowerCamelCase`, for example `efficientInformationMatrix`.
- Inside a `snake_case` name, an `UpperCamelCase` name is written in `lowerCamelCase`, as in
  `isPDonsker_of_finite_bracketing_entropy_integral`.
- Names describe the statement. Equation numbers and other source labels belong in the docstring.
- Hypothesis names are short and descriptive (`h_qmd`, `hJ`, etc.).

Formatting:

- Lines have at most 100 characters.
- Continuation lines of a statement are indented by 4 spaces and proofs by 2 spaces; `by` ends the
  line before the first tactic.
- `·` focuses on a goal.
- `:`, `:=` and infix operators have a space on each side: `(x : ℝ)`, `a / b`, `x ^ 2`.
- Functions are written with `fun`; `λ` and `$` are not used (`<|` replaces `$`).
- Declarations contain no empty lines.

Linters and options:

- An intentional exception to a linter is written as `set_option linter.<name> false in` (or
  `@[nolint <name>]` for environment linters) on the declaration, with a comment giving the
  reason.
- `set_option maxHeartbeats N in` applies to a single declaration and is followed by a comment
  explaining why the proof needs it.
- `open Classical` is not used; use `open Classical in` before a definition or the `classical`
  tactic inside a proof.
- A file longer than 1500 lines states its length limit with `set_option linter.style.longFile N`.

Documentation:

- A file starts with its imports, followed by a `/-! … -/` module docstring that describes the
  file's contents and cites its sources.
- Every definition, structure, structure field and class has a docstring, and so does every main
  theorem.

### Website (TypeScript / React)

- Run `npm run build` to type-check before committing.
- Informal statements in `results.json` must not contain Lean-style notation —
  translate all hypotheses to standard mathematical language and LaTeX.
- The `informal` field may contain HTML (`<span data-link="hN">…</span>` for
  hover-linking, `<p>`, `<strong>`, etc.) but all math must use `$…$` or
  `$$…$$` KaTeX delimiters.

## License

By contributing, you agree that your contributions will be licensed under the
[Apache License 2.0](LICENSE).
