Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`. Never `lake update`.

# TASK
Create `StatLean/ConcentrationInequalities/Maximal/CoveringNumbers.lean`
(namespace `StatLean.ConcentrationInequalities`) — the ε-net / covering-number vocabulary of
Lu *Big Data Analysis* §4.2 (def `ε-Net`, and the covering number `N(X,d,ε)`).

FIRST: search Mathlib for an existing notion — `./tools/loogle.sh '"coveringNumber"'`,
`./tools/loogle.sh '"IsCover"'`, check `Mathlib.Topology.MetricSpace.*` and
`Mathlib.MeasureTheory.Covering.*`. If Mathlib already has a usable `ε`-net / external-covering
number with the right shape (a finite set `N ⊆ s` such that every `x ∈ s` is within `ε` of some
`y ∈ N`, and the min-cardinality over such `N`), **re-export / thin-wrap it** with book-named
defs and a docstring tying it to Lu §4.2 — do NOT reinvent. Only define from scratch if Mathlib's
shape does not fit.

Provide (book §4.2):
1. `def IsEpsilonNet (N : Set X) (s : Set X) (ε : ℝ) : Prop` — `N ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ N, dist x y ≤ ε`
   (in a `[PseudoMetricSpace X]`). Docstring: Lu §4.2 Definition (ε-Net).
2. `def coveringNumber (s : Set X) (ε : ℝ) : ℕ∞` (or `ℕ` with a finiteness hypothesis) — the minimum
   cardinality of a *finite* ε-net of `s`. Docstring: Lu §4.2 covering number `N(s, d, ε)`.
   Pick the encoding (`ℕ∞ := ⨅ …` over finite ε-nets, or `sInf` of cardinalities) that downstream
   `CoveringBall.lean` (which will prove `coveringNumber (ball 0 1) ε ≤ (1+2/ε)^d`) and
   `L2Maximal.lean` can consume cleanly. If Mathlib's `coveringNumber` exists, prefer it.
3. A trivial sanity lemma (e.g. a smaller ε gives a ≥ covering number, OR an ε-net of a finite set
   exists) — just enough that the defs are non-vacuous and usable. ZERO sorry.

No book USER-INPUT hypotheses (pure def layer); tag any added regularity `-- LEAN-ONLY: …`. Each
`def` gets a docstring naming the Lu §4.2 concept it formalizes + edge behavior (empty set, ε ≤ 0).

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/Maximal/CoveringNumbers.lean`. Do NOT touch
the umbrella, `StatLean.lean`, lakefile/manifest/toolchain, `notes/`.

# BUILD
  srun -p shared -c 8 --mem=24G -t 0:30:00 lake build StatLean.ConcentrationInequalities.Maximal.CoveringNumbers

# DONE = build exits 0; ZERO sorries; docstrings; small commit
(`conc(maximal): ε-net + covering number defs (Lu-BDA §4.2)`). Print declaration names, build
status, and whether you reused a Mathlib covering notion or defined fresh (and why).
