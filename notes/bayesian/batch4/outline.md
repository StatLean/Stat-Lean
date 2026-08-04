# Bayesian Batch 4 — vdV Chapter 10 (Bayes Procedures)

Reference: van der Vaart, *Asymptotic Statistics* (1998), Chapter 10, pp. 138–152.
Scope (user-confirmed): **Thm 10.1 (Bernstein–von Mises) + Lemma 10.3 (exponential tests) +
Thm 10.8 (Bayes point estimators) + Thm 10.10 (Doob consistency) + the efficient-centering
corollary** (posterior ≈ N(θ̂ₙ, (nI)⁻¹), p. 144). Deferred: Lemmas 10.4/10.6/10.7
(uniformly consistent estimators layer).

Full plan: `/Users/junweilu/.claude/plans/plan-for-formalizing-batch-optimized-ripple.md`.

## Dependency tree (statement-first; all stubs frozen on `bay/batch4`)

```
ForMathlib bricks
├── AS/ForMathlib/MultivariateGaussianDensity  (constant-free density, tilt, λ-comparisons,
│     tails, loss-convolution continuity)                                [lane bvm-bricks]
├── AS/ForMathlib/ContiguityIntegralComparison (support-free Le Cam 1 + comp_subseq)
├── Bay/ForMathlib/TVDist       (triangle, map, cond, withDensity, Jensen, kernel-meas)
├── Bay/ForMathlib/GaussianTV   (same-cov KL + Pinsker mean-shift TV bound)
└── Bay/ForMathlib/IIDSeqKernel (θ ↦ (Kθ)^⊗ℕ kernel + Fin-n restriction)  [lane doob-core]

BernsteinVonMises/
├── Defs (localScale/localPosterior/effScore/gaussian/TV; tests + prior predicates)  [laptop]
├── ScoreTest → TestBoost → ExponentialTests            (= Lemma 10.3)   [lane bvm-tests]
├── PriorSmallBall → MixtureContiguity → PosteriorConcentration (= Step A)
│                                            [lanes bvm-conc / bvm-local]
├── LocalApproximation                        (= Step B)                 [lane bvm-local]
└── PosteriorNormality → EfficientCentering          (assembly)                 [lane bvm-assembly]

BayesEstimators/
├── Defs (SeparatedLoss/PolyGrowth/risk process/limit criterion)         [laptop]
├── PosteriorTails (10.9) + ArgminConsistency (deterministic)            [lane bpe-aux]
├── UniformApproximation (majorant form; consumes Thm 10.1)              [lane bpe-approx]
└── PointEstimatorLimits (tightness + assembly + Anderson corollary)              [lane bpe-final]

DoobConsistency/
├── Defs (doobJoint/doobData/doobSigma/StronglyConsistentAt)             [laptop]
├── PosteriorMartingale (σ-algebra identities, condDistrib=posterior, Lévy upward)
├── Accessible (SLLN + countable determining family + Lusin–Souslin retraction = (10.11))
└── PosteriorNormality0 (assembly)                                              [lane doob-core]
```

## Key design decisions (details in the plan file)

- Posterior object: Mathlib's canonical `κ†π`; a.e.-identities discharged under `P^n_{θ₀}`
  via the mixture-contiguity swap (`measure_tendsto_zero_of_predictive_null`).
- Per-`h` contiguity is SUPPORT-FREE (via `productMeasure_integral_comparison_boundedMeasurable`
  + new `mutuallyContiguous_of_log_normal_of_integral_comparison`) — do NOT use
  `contiguous_local_alternatives` (needs a same-support hypothesis vdV doesn't grant).
- Step B uses TRUE product densities (`∏ᵢ p_θ(ωᵢ)`), never `exp ∘ logLikelihood`.
- `tvDist` is sup-form = ½ · vdV's L¹ norm (immaterial for →0 statements).
- Δ_{n,θ₀} carries `J⁻¹` (ch-10 convention): `bvmEffScore = toEuclideanCLM J⁻¹ ∘ scoreSum`.
- Thm 10.8: argmax-CMT/ℓ^∞(K) route replaced by recentred majorant approximation +
  deterministic argmin consistency; approximate-argmin hypothesis (εₙ → 0) generalizes the
  book's exact minimizer; conclusion strengthened to in-probability convergence of
  `√n(Tₙ−θ₀) − Δₙ` to the unique argmin `u₀` (weak convergence follows).
- Thm 10.10: generalized to standard-Borel 𝓧 + Polish Θ; vdV Lemmas 10.12/10.13 absorbed by
  an explicit Lusin–Souslin retraction; consistency in ball form.
- Efficient centering: "θ̂ₙ efficient" = the Thm-8.14 expansion `√n(θ̂ₙ−θ₀) − Δₙ →ᵖ 0`
  (USER-INPUT); Gaussian mean-shift TV via same-cov KL + Pinsker.

## Deferred / follow-ups

- Lemmas 10.4, 10.6, 10.7 (tests from uniformly consistent estimators; TV-separability).
- Bridge from `RegularEstimatorSequence` (best regularity, vdV Thm 8.14) to the
  efficiency hypothesis of the centering corollary.
- General Scheffé lemma (not needed on the chosen route).
