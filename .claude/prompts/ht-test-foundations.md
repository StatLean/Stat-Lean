# Close the sorries in HypothesisTesting: ForMathlib/{CriticalFunction,QuantileFunction}, Tests/{PValue,Confidence}, NeymanPearson/{Lemma,LeastFavorable}

Lean 4 / Mathlib proof engineer on `StatLean` (read the repo `CLAUDE.md` first). Pin `v4.29.1`.

You are ON the cluster. Iterate with plain foreground `lake build StatLean.HypothesisTesting.ForMathlib.CriticalFunction` and so on, module by module in dependency order. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** these six files:
  `StatLean/HypothesisTesting/ForMathlib/CriticalFunction.lean`,
  `.../ForMathlib/QuantileFunction.lean`,
  `.../Tests/PValue.lean`, `.../Tests/Confidence.lean`,
  `.../NeymanPearson/Lemma.lean`, `.../NeymanPearson/LeastFavorable.lean`.
  Touch nothing else — in particular NOT `Tests/Defs.lean` (frozen, laptop-only). The two
  `ForMathlib` files must keep **Mathlib-only imports**.
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*` and `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample. Honest refusal is the desired outcome, not a failure.
- Commit after each lemma compiles, so work is banked against preemption.
- After green: `#print axioms exists_mostPowerful`, `#print axioms superUniform_nestedPValue`, `#print axioms isConfidenceFamily_of_acceptance` — expect only `propext, Classical.choice, Quot.sound`.

## Order of attack

Prove `QuantileFunction` first — everything else leans on it.

1. **`QuantileFunction`**: `quantile F p = sInf {x | p ≤ F x}`; monotonicity; the Galois lemma `quantile_le_iff` (for monotone right-continuous `F`); **`exists_critical_constants`** — for a probability measure on `ℝ` and `α ∈ (0,1)` there are `C` and `γ ∈ [0,1]` with `P(C,∞) + γ·P{C} = α`. That last one is the randomization constant that the Neyman–Pearson lemma and every subsequent test construction consume; it is the single most reused result in this item. Route: take `C` to be the `(1−α)`-quantile of the law and solve for `γ` by the jump size at `C`; the `0/0` corner is excluded because a jump of size zero forces the continuous case.
2. **`CriticalFunction`**: `randomizedTestKernel` is already defined; prove its `apply`/`apply_one`/Markov/`lintegral` lemmas. Imitate the construction pattern in `StatLean/Minimaxity/LeCam/TwoPoint.lean` (read it; do not import it).
3. **`Tests/PValue`** (Lem 3.3.1): super-uniformity of `nestedPValue`. Only monotonicity of the measure is needed — measurability of the regions is deliberately **not** a hypothesis here; do not add it.
4. **`Tests/Confidence`** (Thm 3.5.1): the duality lemmas. `IsConfidenceFamily P S γ` takes the **coverage** level in the last slot (so a level-α test inverts to `1 − α`); keep that convention.
5. **`NeymanPearson/Lemma`** (Thm 3.2.1 + Cor 3.2.1): existence via `exists_critical_constants`; sufficiency by the standard `(φ − ψ)(p₁ − C·p₀) ≥ 0` pointwise argument integrated against `μ`; necessity/uniqueness a.e. off the boundary set. `Cor 3.2.1` (strict unbiasedness) has a companion `power_eq_alpha_of_eq` covering the degenerate `P₀ = P₁` case — prove both.
6. **`NeymanPearson/LeastFavorable`** (Thm 3.8.1 + Cor 3.8.1): once the lemma is available these are short — the mixture test's size bound transfers to every member of the composite null.

## Note on thresholds

The NP layer uses `ℝ≥0∞` thresholds deliberately, so the `k = ∞` corner is a real case rather than junk. Keep it.

## Report

Final `lake build` status per module, per-file sorry counts, the three `#print axioms` outputs, and any statement you believe is false (with the counterexample).
