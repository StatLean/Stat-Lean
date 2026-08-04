# Close the sorries in HypothesisTesting/ForMathlib/GroupAverageMeasure.lean and Invariance/{MaximalInvariant,UMPInvariantFinite,EquivariantConfidence}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.HypothesisTesting.ForMathlib.GroupAverageMeasure`, then the three `Invariance` modules in dependency order. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** `StatLean/HypothesisTesting/ForMathlib/GroupAverageMeasure.lean`,
  `.../Invariance/MaximalInvariant.lean`, `.../Invariance/UMPInvariantFinite.lean`,
  `.../Invariance/EquivariantConfidence.lean`. Touch nothing else — in particular NOT
  `Invariance/Defs.lean` or `Tests/Defs.lean` (frozen, laptop-only). `GroupAverageMeasure`
  must keep **Mathlib-only imports**.
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*` and `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms isInvariantTest_iff_factors`, `#print axioms exists_isUMPInvariant_of_finite_transitive` — expect only `propext, Classical.choice, Quot.sound`.

## Notes on specific targets

- **`GroupAverageMeasure`**: `groupAverage` is the finite-group symmetrization `|G|⁻¹ ∑_g f (g • x)`. The invariant-sets carrier is deliberately the *set-of-sets* fallback with the σ-algebra `m` passed as a parameter plus a characterization hypothesis `hm_inv` — do not try to package a `MeasurableSpace` instance instead. The load-bearing result is `condExp_eq_groupAverage`: under an invariant `P`, the conditional expectation w.r.t. the invariant σ-algebra is the orbit average a.e. Route: `groupAverage f` is `m`-measurable and satisfies the defining set-integral identity, then `ae_eq_condExp_of_forall_setIntegral_eq`. The set-integral identity is a change of variables `P.map (g • ·) = P` summed over `g`.
- **`MaximalInvariant`**: `InducesOn`/`PreservesFamily` group lemmas are bookkeeping. `isInvariantTest_iff_factors` (Thm 6.2.1) is set-level: (⇐) trivial; (⇒) define `h` on the range of `M` by choice and use orbit-separation. The measurable version carries the book's own structural hypothesis, stated here as a `MeasurableEmbedding (fun x => (M x, Y x))` — use it, it is exactly the "1:1 onto a Borel set with Borel inverse" condition. Thm 6.2.2 (stepwise) transcribes `E*` pointwise through `s`, avoiding a choice off `range s`.
- **`UMPInvariantFinite`** (Thm 6.3.1): the orbit-averaged likelihood-ratio test is UMP invariant for a finite group with transitive induced action. Note the deliberate two-statement split: the headline is on the **sample side** (`orbitAverage` over `g • x`), and `orbitAverage_eq_avg_translated_density` bridges to the source's *parameter-side* average `∑ᵢ p_{ḡᵢθ}(x)/N` under an explicit `G`-invariance hypothesis on the dominating measure. They agree only under that hypothesis — do not conflate them.
- **`EquivariantConfidence`** (Lem 6.11.1): `isEquivariantConfidence_iff_acceptance_equivariant` is the honest iff. The source's part (i) — stabilizer-invariance of `A(θ)` — is strictly weaker and does **not** convert back, so it stays a separate corollary. Keep that separation.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, and any statement you believe is false (with the counterexample).
