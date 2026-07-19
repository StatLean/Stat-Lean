# Close PointEstimation tail: LinearModel/{LeastSquares,Equivariant}, ExponentialFamily/{Smoothness,MinimalSufficient}, Equivariance/{LocationMRE,LocationExamples,ScaleMRE}

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session. **Work the files sequentially, committing each as it compiles**, to avoid races in the shared worktree.

## Hard constraints

- **Only edit** those seven files. Do NOT touch `ScaleStructure.lean` — its `mpr` is a confirmed genuine falsity (non-Borel subset of `{xₙ=0}`), left as a documented obstruction.
- Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors** on the reachable targets below. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — nine such reports have been acted on this campaign, five of them false/unprovable statements caught with counterexamples. That is the highest-value output.
- Commit after each lemma compiles.

## Reachable targets (do these; skip what your predecessor flagged as blocked)

1. **`LocationExamples.isLocMRE_mean_gaussian`** — a predecessor delegated this and reported it "building now". `Pitman.lean` is 0-sorry, so the route is: the Gaussian location Pitman ratio evaluates in closed form to `X̄` by completing the square in the exponent. Finish it. Do NOT attempt Kagan–Linnik–Rao.
2. **`LeastSquares` (3)** — orthonormal-basis transport `linearModelFull → canonicalModel` (Canonical is fully closed). `ProbabilityTheory.stdGaussian_map (f : E ≃ₗᵢ[ℝ] F)` exists; still needed: the affine bridge `gaussianVector ξ σ² = (stdGaussian _).map (√σ²•· + ξ)`, the basis-extension isometry (`Orthonormal.exists_orthonormalBasis_extension`), and `IsUMVU` transport along a measurable sample-space equiv (`RandomDesign.isUMVU_reparam` is the template).
3. **`MinimalSufficient` (2)** — Cor 6.16, Doob–Dynkin log-likelihood inversion on top of the closed `Completeness.ExpFamily`/`Sufficiency` stack.
4. **`Equivariant` (4)** — canonical/subspace MRE clauses; Gaussian conditional-risk minimization in canonical coordinates plus the χ² moment minimization (`residualScaleConst_one` closed).
5. **`Smoothness` (3 of 4)** — continuity + `HasFDerivAt` for `η ↦ ∫ f·e^{⟪η,T⟫} dν` on the interior via `hasFDerivAt_integral_of_dominated_loc_of_lip` + the `2^s` sign-vector envelope. `analyticOnNhd_integral_exp_inner` is a SANCTIONED DEFERRAL — leave it.

## Known-blocked — leave as documented debts, do NOT force

- `LocationMRE.exists_measurable_condMinimizer_convex` and `ScaleMRE.exists_isScaleMRE_of_convex`: both feed `ForMathlib.MeasurableArgmin.exists_measurable_argmin`, whose **continuity** hypothesis genuinely fails for their objective (convex but can jump finite→∞ at its finiteness boundary). This is a known brick-design issue awaiting a scope decision; leave both with their notes and report if you find a way around it without the brick.

## Closed, axiom-clean — black boxes

`ForMathlib` (all 8); `ExponentialFamily/{Basic,MGF,NaturalStatistic}`; `Sufficiency/*`; `Completeness/{Basu,ExpFamily}`; `UMVU/{Basic,CovarianceCriterion,RaoBlackwell}`; `InformationInequality/{Basic,CramerRao,Additivity,Multiparameter}`; `Equivariance/{General,LocationStructure,ConditionalRiskEngine,RiskUnbiased,Pitman,ScaleStructure(mp only)}`; `LinearModel/{Canonical,GaussMarkov}`. **Do not route through `isUMVU_of_complete_sufficient`** (sorry-tainted); use `CovarianceCriterion.isUMVU_iff_uncorrelated_unbiasedZero`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms isLocMRE_mean_gaussian`, and for anything left open the precise obstruction.
