# Close the sorries in PointEstimation/Sufficiency/{Basic,RiskEquality,BayesianBridge}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read the repo `CLAUDE.md` first). Pin `v4.29.1`.

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.Sufficiency.Basic` (then `.RiskEquality`, then `.BayesianBridge`). **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/Sufficiency/Basic.lean`, `.../RiskEquality.lean`, `.../BayesianBridge.lean`. Touch nothing else — in particular NOT `Sufficiency/Defs.lean` or `Model/Defs.lean` (frozen, laptop-only).
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*` and `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a `-- TODO:`; report it.
- **Do not weaken any statement.** A statement you believe false should be left sorried and reported with a counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms exists_riskRand_eq_of_sufficient` — expect only `propext, Classical.choice, Quot.sound`.

## Context you need

Two coexisting sufficiency notions live in the frozen `Sufficiency/Defs.lean`:

- `IsSufficient P T` — the classical per-event form: for each measurable `A` a θ-free measurable `κA : S → ℝ≥0∞` satisfying the defining conditional-probability identity on `T`-cylinders.
- `HasSufficientKernel P T` — a single θ-free Markov kernel `Q : S ⇝ 𝓧` disintegrating the **graph** law: `∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q`.

The graph/`⊗ₘ` form was chosen deliberately over the weaker reconstruction form because it pins the kernel to the fibers, which is what `hasSufficientKernel_fiber` and the risk argument need.

Risk lives in `Model/Defs.lean` as `∫⁻` in `ℝ≥0∞` (junk-value discipline): `riskRand P L κ θ = ∫⁻ x, ∫⁻ d, L θ d ∂(κ x) ∂(P θ)`.

## Notes on specific targets

- `isProbabilityMeasure_statLaw`, `statLaw_snd`: bookkeeping. For `statLaw_snd` note Mathlib's `Measure.snd_compProd : (μ ⊗ₘ κ).snd = κ ∘ₘ μ` puts the kernel on the **left** of `∘ₘ` — the file's statement is already shaped to match, don't fight it.
- `isSufficient_of_hasSufficientKernel`: take `κA := fun t => Q t A`; the defining identity falls out of `Measure.compProd_apply` on the rectangle `B ×ˢ A`. Expect un-β-reduced redexes after the rewrite — `simp_rw`/`dsimp only` before the next `rw` (`CLAUDE.md` §7.12).
- `hasSufficientKernel_fiber`: the graph has full measure under the joint law, so the fiber `{x | T x = t}` carries `Q t`-mass 1 for a.e. `t`. Needs `Measurable T` and standard-Borel `S` (both are hypotheses).
- **`exists_riskRand_eq_of_sufficient` (Thm 6.1) should be easy under this definition** — it is kernel-composition associativity plus the second-marginal identity, not a conditional-expectation argument. `κ ∘ₖ Q : Kernel S D` is the T-based randomized estimator. Get the composition order right; there is an ASCII diagram in the file header.
- `BayesianBridge`: `HasSufficientKernel ⇑K T → StatLean.Bayesian.IsSufficient K hT` — take second marginals of the graph identity to land on the Bayesian reconstruction form. Note `Kernel.IsMarkovKernel.comp` lives in the `ProbabilityTheory.Kernel` namespace (`CLAUDE.md` §7.16).

## Report

Final `lake build` status for each module, per-file sorry counts, the `#print axioms` output, and any statement you believe is false.
