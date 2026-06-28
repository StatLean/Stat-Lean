# Close Prop 15.1, the MI convexity bound (15.34), and Gaussian KL (Ex 15.13)

Lean 4 / Mathlib proof engineer on **StatLean** (read `CLAUDE.md` §2,§6,§7). Pin `v4.29.1`. ON cluster
inside `srun` — iterate to 0 errors/0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/EstimationToTesting.lean`
- `StatLean/Minimaxity/Fano/MutualInformation.lean`
- `StatLean/Minimaxity/ForMathlib/GaussianKL.lean`
Keep signatures, tags, citation docstrings UNCHANGED. No `axiom`/`admit`. Helpers `private`.

## Proofs
- `minimax_ge_testing_error` (Prop 15.1): `Φ δ * multiwayTestingError (P.comap θfam hθ) ≤ minimaxRiskDist Φ g P`.
  Chain: `multiwayTestingError = bayesRisk (zeroOneLoss) (P.comap…) (uniformPrior)` (defn);
  `bayesRisk_le_minimaxRisk` (Mathlib `ProbabilityTheory`) bounds it by `minimaxRisk (zeroOneLoss) (P.comap…)`;
  then the geometric step: the loss `distortionLoss Φ g (θfam j) y = Φ(edist (g (θfam j)) y) ≥ Φ δ · 𝟙[nearest-point test errs]`
  using `IsSeparatedFamily` + `edist_triangle` + `Monotone Φ`, giving `Φ δ · minimaxRisk(zeroOneLoss…) ≤ minimaxRisk(distortionLoss…)=minimaxRiskDist`.
  Use `ProbabilityTheory.minimaxRisk`/`bayesRisk` defs + monotonicity of `⨅`/`⨆`/`∫⁻`. This is the central
  theorem — invest here. If a sub-step resists, lift it to a `private` named lemma (sorry) + report.
- `mutualInformation_le_avg_pairwise_kl` (15.34): `I ≤ (1/M²) Σⱼₖ klDiv (Q j)(Q k)`. Convexity of `klDiv`
  in the 2nd arg: `klDiv (Q j) Q̄ = klDiv (Q j) ((1/M)Σ Q k) ≤ (1/M)Σₖ klDiv (Q j)(Q k)` (Jensen). If the
  ℝ≥0∞ convexity of klDiv resists, lift to `private klDiv_le_avg` (sorry) + report.
- `klDiv_gaussianReal` (Ex 15.13): `klDiv (gaussianReal m₁ v)(gaussianReal m₂ v) = ofReal((m₁−m₂)²/(2v))`.
  Use the explicit `gaussianReal` density `gaussianPDFReal` / `gaussianReal_apply` and `klDiv` via `llr`:
  `llr = log(p₁/p₂) = ((x−m₂)²−(x−m₁)²)/(2v)`, integrate against `gaussianReal m₁ v` (mean `m₁`, var `v`).
  Search `ProbabilityTheory.gaussianReal_…`, `klDiv_eq_integral_llr`. Concrete; invest. Debt+report if stuck.

## DONE
`grep -c sorry` = 0 per file (or only reported named debts). Report closed/debt + key lemmas used.
