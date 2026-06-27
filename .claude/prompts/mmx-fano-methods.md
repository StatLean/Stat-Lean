# Close Fano method theorems: FanoLowerBound (15.31/Prop 15.12), LocalPacking (15.35), YangBarron (15.21)

Lean 4 / Mathlib proof engineer on **StatLean** (read CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster.
Run every `lake build` SYNCHRONOUSLY in the FOREGROUND (never background; never end turn mid-build).
Iterate to 0 errors / 0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/Fano/FanoLowerBound.lean`
- `StatLean/Minimaxity/Fano/LocalPacking.lean`
- `StatLean/Minimaxity/Fano/YangBarron.lean`
Keep signatures, tags, citation docstrings UNCHANGED. No axiom/admit. Helpers `private`. Black-box use of
`minimax_ge_testing_error` (Prop 15.1), `mutualInformation`/`mutualInformation_le_avg_pairwise_kl`,
`discreteEntropy`/`discreteCondEntropy`/`discreteCondEntropy_le_entropy` (Entropy.lean), `klDiv`.

## Proofs
- `fano_inequality` (15.31): `1 − (I+log2)/log M ≤ multiwayTestingError Q`. Go through the entropy form
  (Eq 15.61): with `J` uniform on `Fin M` and the test, `H(J|Z) ≤ h(q_e) + q_e log(M−1)`; combine
  `H(J|Z)=H(J)−I=log M−I`, `h(q_e)≤log2`. Use the `Entropy.lean` discrete-entropy lemmas. This is the
  hard crux of the chapter — if the full measure-theoretic `H(J|Z)` (continuous `Z`) resists, lift to a
  `private` lemma `fano_entropy_form` (single sorry + `-- TODO(mmx): Eq 15.61`) and derive 15.31 from it.
- `minimax_fano_lower_bound` (Prop 15.12): compose `minimax_ge_testing_error` with `fano_inequality`
  (monotonicity: `Φ δ * (1 − …) ≤ Φ δ * testingError ≤ minimaxRiskDist`). Mostly `gcongr`/`mul_le_mul`.
- `minimax_local_packing` (15.35): from `minimax_fano_lower_bound` + `mutualInformation_le_avg_pairwise_kl`
  + hypotheses h35a/h35b: bound `I ≤ c²nδ²`, so `(I+log2)/log M ≤ ½` (from h35b), giving `½ Φ(δ)`. Algebra
  in ℝ≥0∞ (ofReal monotonicity, `ENNReal.ofReal_le_ofReal`). Lift hard cruxes to named sorries if needed.
- `yang_barron` (15.21): `I ≤ ε² + log N`. From the mixture form `I = (1/M)Σ D(P_j‖Q̄)` and the cover
  `D(P_j‖γ_{k(j)}) ≤ ε²`, with `Q = (1/N)Σ γ_k`: `D(P_j‖Q) ≤ D(P_j‖γ_{k(j)}) + log N`. Use `klDiv` algebra
  / the mixture-minimizes-KL bound. Lift the `log N` step to a named sorry if it resists.

## DONE
`grep -c sorry` per file = 0 (or only reported named debts). `git add` ONLY the three touch-set files,
then commit. Report closed/debt per theorem + key lemmas.
