# Close the sorries in HypothesisTesting/ForMathlib/HypergeometricMoments.lean and Randomization/{ExactLevel,OrbitConditional}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Build in order: `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments`, then `.Randomization.ExactLevel`, then `.Randomization.OrbitConditional`. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** those three files. Touch nothing else — NOT `Randomization/Defs.lean` or `Invariance/Defs.lean` (frozen, laptop-only). `HypergeometricMoments` must keep **Mathlib-only imports**.
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*`, import closed project modules (into the two `Randomization` files only), and add `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample. Honest refusal is the desired outcome.
- Commit after each lemma compiles.
- After green: `#print axioms randTest_exact_level`, `#print axioms superUniform_randPValue` — expect only `propext, Classical.choice, Quot.sound`.

## Why this item is high value

**`randTest_exact_level` is the cleanest headline in the whole batch**: exact finite-sample level `α`, no asymptotics, no regularity conditions — pure finite-group combinatorics. It is the foundation the entire permutation-test chapter rests on.

## The core argument (verified against the source)

Everything follows from the **pointwise orbit identity** `sum_randTest_orbit`:
for every `x`, `∑_{g ∈ G} randTest G T α (g • x) = |G| · α`.

The frozen construction: `k = |G| − ⌊|G|·α⌋` is the critical index, `T^{(k)}` the `k`-th smallest
orbit value, `M⁺` the count strictly above it, `M⁰` the count equal to it, and
`a(x) = (|G|α − M⁺)/M⁰` the boundary weight; the test is `1` above, `a(x)` at, `0` below.
Summing over the orbit: the `M⁺` values above contribute `M⁺`, the `M⁰` boundary values
contribute `M⁰ · a(x) = |G|α − M⁺`, and the rest contribute `0` — total `|G|α`. **Note there is
NO integrality caveat**: the identity is exact for every `x`; `a(x)` absorbs the fractional part.
What `0 < α < 1` buys is `k ∈ {1,…,|G|}` (keeping `T^{(k)}` off `orbitOrderStat`'s junk branch)
and `M⁰ ≥ 1` (the identity element contributes, so no `0/0` in `a(x)`). Establish those two facts
first as `private` helpers — they are the only side conditions the argument needs.

Then `randTest_exact_level` is: average the orbit identity over `G` and use the randomization
hypothesis `P.map (g • ·) = P` to see each `∫ randTest(g • ·) dP = ∫ randTest dP`; so
`|G| · ∫ randTest dP = ∫ (∑_g randTest(g • x)) dP = |G|α`.

`superUniform_randPValue` ((17.6)) is the same counting argument applied to
`p̂ x = |G|⁻¹ #{g : T x ≤ T (g • x)}`, giving `P{p̂ ≤ u} ≤ u` — state it against
`StatLean.MultipleTesting.SuperUniform` (that definition is `∀ t ≥ 0, μ {p ≤ t} ≤ ofReal t`).

## `OrbitConditional`

`condExp_orbit_eq_orbitAverage` — the conditional expectation given the invariant σ-algebra is
the orbit average. The file defines its own `invariantSigmaAlgebra` (a real `MeasurableSpace`
instance) and proves `invariantSigmaAlgebra_le`. Route: the orbit average is invariant-measurable
and satisfies the defining set-integral identity (change of variables `g` by `g`, summed), then
`ae_eq_condExp_of_forall_setIntegral_eq`. **Note** `ForMathlib/GroupAverageMeasure` states a
general version (`condExp_eq_groupAverage`) but that file is **still open** — prove this one
self-contained rather than importing a sorried lemma, and say so in your report.
Also note the set-form statement uses `Set.indicator`, not `if … then … else` (arbitrary sets
are not decidable) — keep it that way.

## `HypergeometricMoments`

Sampling without replacement, `m` of `n`, on `SubsetsOfCard n m` with `PMF.uniformOfFintype`:
`E Wᵢ = m/n`; `E WᵢWⱼ = m(m−1)/(n(n−1))` for `i ≠ j`; the covariance formula; and the `O(1/m)`
variance bound for `∑ cᵢWᵢ`. Pure finite counting — `Finset.card` bijections between
`{s : card = m, i ∈ s}` and `{s' ⊆ univ \ {i} : card = m−1}`. `0 < n` and `2 ≤ n` are supplied by
`i : Fin n` and `i ≠ j` respectively — the file already omits them; don't add them back.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, and any statement you believe is false (with the counterexample).
