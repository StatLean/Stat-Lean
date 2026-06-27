# Close Le Cam method theorems: TwoPoint (15.13/14), ConvexHull (15.9), Functional (Cor 15.6)

Lean 4 / Mathlib proof engineer on **StatLean** (read CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster.
Run every `lake build` SYNCHRONOUSLY in the FOREGROUND (never background; never end your turn mid-build).
Iterate to 0 errors / 0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/LeCam/TwoPoint.lean`
- `StatLean/Minimaxity/LeCam/ConvexHull.lean`
- `StatLean/Minimaxity/LeCam/Functional.lean`
Keep signatures, tags, citation docstrings UNCHANGED. No axiom/admit. Helpers `private`. You MAY use,
as black boxes, the already-stated theorems in `StatLean.Minimaxity` (some may themselves be `sorry` —
that is fine, call them): `minimax_ge_testing_error` (Prop 15.1), `tvDist`/`tvDist_*`,
`sqHellinger`/`hellingerModulus`, `multiwayTestingError`, `bayesRisk`/`minimaxRisk` (Mathlib).

## Proofs
- `binary_testingError_eq_tvDist` (15.13): `multiwayTestingError Q = ½(1 − tvDist (Q 0)(Q 1))` for
  `Q : Kernel (Fin 2) 𝓧`. Unfold `multiwayTestingError`/`bayesRisk`; the optimal test is the likelihood-
  ratio test; relate the Bayes error to `tvDist` (sup form). Decompose `Fin 2` sum; use `uniformPrior`
  (mass ½ each). Hard step is the inf-over-tests = ½(1−TV) — if it resists, lift to a `private` named sorry.
- `minimax_two_point` (15.14): specialize `minimax_ge_testing_error` to `M=2` with `θfam = ![θ₀,θ₁]`,
  then rewrite the testing error via `binary_testingError_eq_tvDist`. Build `θfam : Fin 2 → Θ`
  (`Matrix.cons`/`Fin.cons`), check `IsSeparatedFamily` from `hsep`, and `Φ δ/2·(1−TV) = Φ δ·½(1−TV)`.
- `minimax_le_cam_convex_hull` (Lemma 15.9): from `minimax_ge_testing_error` plus the data-processing /
  variational TV (`one_sub_tvDist_eq_iInf`) applied to the mixtures `P.comap a₀ ∘ₘ π₀`, `…∘ₘ π₁`. The
  convexity step (sup over mixtures) — if it resists, lift the crux to a `private` named sorry.
- `minimax_functional_modulus` (Cor 15.6): apply `minimax_two_point` to the pair achieving the modulus
  `hellingerModulus θfunc P (1/(2√n))`, bound TV by the Hellinger tensorization (`sqHellinger_pi_le_nsmul`,
  Lemma 15.3 `lecam_tv_le_hellinger`): `‖Pⁿ_f − Pⁿ_g‖_TV ≤ ¼`, giving the `¼ Φ(½ ω)` bound. Several
  steps; lift hard cruxes to named `private` sorries if needed.

## DONE
`grep -c sorry` per file = 0 (or only reported named debts). `git add` ONLY the three touch-set files,
then commit. Report closed/debt per theorem + key lemmas.
