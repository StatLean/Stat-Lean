# Searching Mathlib — tool reference

One page. Pick the tool that matches the query type.

## Decision table

Two divisions: **known target** (you have a name, file, or qualified concept) vs. **unknown target** (concept, informal description, or shape).

### Known target

| Query | Tool | Where |
|---|---|---|
| "There's a hole — is there a single lemma that closes it?" | `exact?` / `apply?` | Inside a `by` block |
| "Is there a rewrite that makes progress?" | `rw?` | Inside a `by` block |
| "Did **we** already prove a lemma about X in this project?" | `./tools/where.sh <name-substring>` (or `--doc <text>`) | CLI, local, instant |
| "Does this exact name exist? What's its type?" | `./tools/check.sh '<expr>'` | CLI, local, instant |
| "What lemmas does this file expose?" | `./tools/api.sh <lean-file>` | CLI, local, instant |
| "Browse what's in a namespace" | [mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/) | Browser |

### Unknown target

| Query | Tool | Where |
|---|---|---|
| "Find 'Cauchy-Schwarz for L² integrals'" — concept / folk name / informal description | `./tools/explore.sh '<query>'` | CLI wrapper around [leanexplore.com](https://www.leanexplore.com) — needs API key. **Default for any unknown-name query.** |
| Same query in-Lean (no API key) | `#leansearch` / `#moogle` | In a scratch `.lean` file, see below |
| "Find a lemma whose conclusion looks like `_ + _ ≤ _`" — type-shape | `./tools/loogle.sh '<pattern>'` | CLI wrapper around [loogle.lean-lang.org](https://loogle.lean-lang.org) |
| Partial-name guess `'"sqrt_add"'` | `./tools/loogle.sh '"<substring>"'` | Same |

## Examples

### `tools/check.sh` — instant name verification

```bash
./tools/check.sh 'abs_add_le'
# → abs_add_le : ∀ (a b : α), |a + b| ≤ |a| + |b|

./tools/check.sh 'MemLp.integrable_mul'
# → MemLp.integrable_mul : ...

./tools/check.sh 'foo_bar_baz'      # typo or doesn't exist
# → unknown identifier 'foo_bar_baz'
```

### `tools/api.sh` — list declarations in a file

Quick orientation when re-entering a file after a gap. Shows line number, kind, and name of every top-level declaration; skips anonymous `instance` blocks.

```bash
./tools/api.sh StatLean/AsymptoticStatistics/DQM/Properties.lean
#   L53     lemma                 dqm_residual_eventually_memLp
#   L122    lemma                 dqm_score_memLp_two
#   L179    lemma                 dqm_fisher_integrable
```

For a full signature, open the file at the reported line or run `./tools/check.sh '<Namespace.name>'`.

### `tools/where.sh` — search *our* declarations across the project

Project-local complement to `loogle.sh` / `explore.sh` (which both search Mathlib). Walks `StatLean/**/*.lean` looking at every top-level declaration. **First stop when you suspect we already have a lemma but can't remember where.**

```bash
./tools/where.sh score                      # name substring (case-insens.)
./tools/where.sh --exact ScoreFunction      # exact local-name match
./tools/where.sh --in AsymptoticStatistics/DQM residual  # only that subtree
./tools/where.sh --kind theorem residual    # only theorems / lemmas / defs / …
./tools/where.sh --doc 'score function'     # docstring contains text
```

Output: `path/file.lean:Lline  kind  name`, plus the docstring's first line in `--doc` mode. Take any hit's name and pipe through `./tools/check.sh '<Namespace.name>'` for the full signature. Exits 1 with a clear message on no-match.

Pure shell (`find` + `awk`); no Lean toolchain or network needed.

### `tools/loogle.sh` — type-pattern search

Wraps the Loogle Web API. Needs `curl` + `jq` (both typically preinstalled; `brew install jq` if missing) and network access. Zero Lean build cost — no `lake update` required, so **portable to any machine that clones the repo** without additional setup.

```bash
./tools/loogle.sh 'Real.sqrt ?x'        # lemmas mentioning Real.sqrt applied to something
./tools/loogle.sh '|?a + ?b| ≤ _'       # lemmas whose conclusion fits this shape → finds abs_add_le, …
./tools/loogle.sh '"sqrt_add"'           # name substring match (inner quotes)
./tools/loogle.sh '_ * _ < _ * _'        # pure type-pattern search, no name constraint
```

Set `LOOGLE_LIMIT=N` to change the default 15-result cap. Full pattern syntax: https://loogle.lean-lang.org.

### `tools/explore.sh` — semantic / natural-language search (CLI)

Wraps the [LeanExplore](https://www.leanexplore.com) Web API. Same query style as `#leansearch` / `#moogle` ("Cauchy-Schwarz for L² integrals", "central limit theorem iid"), but from the shell — no scratch `.lean` file or `lake env lean` round-trip.

```bash
./tools/explore.sh 'Cauchy-Schwarz for L² integrals'
./tools/explore.sh 'central limit theorem for iid sequence'
LEANEXPLORE_LIMIT=20 ./tools/explore.sh 'score function has zero expectation'
LEANEXPLORE_PACKAGES="Mathlib,Std" ./tools/explore.sh 'compact image of continuous'
```

**One-time setup (per machine):** the LeanExplore API requires Bearer-token auth, so unlike `loogle.sh` this is **not** zero-setup.

1. Register at https://www.leanexplore.com (free) to get an API key.
2. `export LEANEXPLORE_API_KEY=...` (add to `~/.bashrc` / `~/.zshrc`).

Without the key, the script exits 2 with a clear setup hint. On a fresh machine, fall back to `loogle.sh` (no key needed) or `#leansearch` / `#moogle` in a scratch file.

Output prints `name`, the source-text first line (the signature), the docstring's first line if present, and the module path — one block per hit.

### `#leansearch` / `#moogle` — natural-language search

`LeanSearchClient` is transitively installed via Mathlib. Drop into a scratch `.lean` file:

```lean
import Mathlib
import LeanSearchClient

#leansearch "Chebyshev inequality variance"
#moogle "score function has zero expectation"
```

Run with `lake env lean scratch.lean` (or just view in an editor with the Lean extension). Returns ranked candidates with full signatures. Needs network.

### `exact?` / `apply?` / `rw?` — in-proof search

Inside a `by` block, with the goal visible:

```lean
example (hX : MemLp X 2 μ) (hc : (0 : ℝ) < 1) :
    μ {ω | 1 ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / 1 ^ 2) := by
  exact?
  -- Lean suggests: exact meas_ge_le_variance_div_sq hX hc
```

Zero-setup, context-aware. Always try this first inside a proof before reaching for anything else.

## Picking tools in practice

* `exact?` / `apply?` / `rw?` — always try **inside** a proof before reaching for any of the below.
* `where.sh` — **first choice for "did *we* already prove this"**. Always check our own code before searching Mathlib — same lemma proved twice is wasted effort.
* `check.sh` — first choice for "does this exact name exist / what's its type".
* `api.sh` — first choice when you know the home file but not the exact name.
* **`explore.sh` — default for any unknown-name search.** Folk/textbook names (CLT, LLN, Girsanov, Slutsky, …) and Mathlib-style concept descriptions ("Cauchy-Schwarz for L² integrals") both. Empirically the strongest unknown-name tool — reach for this *before* loogle when you don't have a precise type shape. Requires `LEANEXPLORE_API_KEY`; if missing, fall through to `#leansearch` / `#moogle` (same algorithm, in-Lean).
* `loogle.sh` — **type-shape specialist.** First choice when you know the *shape* (`|?a + ?b| ≤ _`, `_ * _ < _ * _`) but not the name. Also the partial-name lookup `'"sqrt_add"'` for guess-the-name searches. Don't reach for it as a generic unknown-name fallback — explore.sh wins on concept / folk-name queries.
* `#leansearch` / `#moogle` — same algorithm as `explore.sh`, but in a scratch `.lean` file. Use when no `LEANEXPLORE_API_KEY` is set, or when you'd rather see results next to a Lean buffer.

All search tools need network; only `exact?` and friends work offline. If consistently doing offline work, consider adding Loogle as a lake dep (`require loogle from ...`), at the cost of ~5 min to the next `lake update`.
