# Close Fano's inequality (Eq 15.61/15.31) + Yang–Barron cover (Lemma 15.21)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/Fano/FanoLowerBound.lean`  (`fano_inequality` crux)
- `StatLean/Minimaxity/Fano/YangBarron.lean`      (`yang_barron` crux)
Keep public signatures/docstrings UNCHANGED. Helpers `private`. Use `Entropy.lean` (discreteEntropy/
discreteCondEntropy/discreteMutualInfo + `discreteCondEntropy_le_entropy`) and `mutualInformation`,
`klDiv`, `klDiv_mixture_minimizes` (may be proven in parallel) as black boxes.

## `fano_inequality`: `1 − (I + log2)/log M ≤ multiwayTestingError Q`  (HARD — entropy Fano)
Eq 15.61 route: with `J` uniform on `Fin M`, observation `Z ∼ Q J`, and an arbitrary test `ψ : 𝓧 → Fin M`
(here built from the estimator), the standard Fano `H(J|Z) ≤ h(qₑ) + qₑ log(M−1)` where `qₑ = P[ψ≠J]`.
Then `I(Z;J) = H(J) − H(J|Z) = log M − H(J|Z)`, `h(qₑ) ≤ log 2`, giving `qₑ ≥ 1 − (I+log2)/log M`.
The continuous-`Z` conditional entropy `H(J|Z)` needs the discrete posterior of `J` given `Z` (a finite
distribution on `Fin M`) integrated over `Z` — build via Mathlib `ProbabilityTheory.condDistrib` /
disintegration of the joint `(Z,J)` law, or work directly with the `bayesRisk` form and the discrete
`Entropy.lean` lemmas applied to the posterior. This is genuinely hard and may need new infrastructure —
if the full continuous-`Z` argument resists, isolate the crux as ONE named `private` lemma
`fano_entropy_continuous` (single sorry + precise `-- TODO(mmx)`) and prove everything around it
(the algebra `I = log M − H(J|Z)`, `h(qₑ) ≤ log2`, the rearrangement).

## `yang_barron`: `I ≤ ε² + log N`  given an ε-cover `{γ k}` in √KL (`klDiv (Q j) (γ k) ≤ ε²`)
`I = (1/M)Σ_j klDiv (Q j) Q̄`. Take `Q := (1/N)Σ_k γ k`. By `klDiv_mixture_minimizes` (mixture minimizes
avg KL), `(1/M)Σ_j klDiv (Q j) Q̄ ≤ (1/M)Σ_j klDiv (Q j) Q`. For each `j`, `klDiv (Q j) ((1/N)Σγ) ≤
klDiv (Q j) γ_{k(j)} + log N` (drop other mixture terms: `(1/N)Σγ ≥ (1/N)γ_{k(j)}` ⇒ `dQj/dQ ≤ N·dQj/dγ`,
so `∫ log(dQj/dQ) dQj ≤ ∫ log(dQj/dγ) dQj + log N`). With `klDiv (Q j) γ_{k(j)} ≤ ε²`, get `I ≤ ε² + log N`.
Build the `klDiv (P) (mixture) ≤ klDiv (P) (component) + log N` lemma (the load-bearing step).

GOAL: close both; reduce residuals to SMALLER named `private` sorries + precise `-- TODO(mmx)`.
## DONE: build both modules green; `git add` ONLY the two files; commit. Report closed/residual + lemmas.
