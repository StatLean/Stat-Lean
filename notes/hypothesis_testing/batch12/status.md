# HypothesisTesting Batch 12 — orchestration status

Last update: 2026-07-15 (campaign start; design frozen, stubs pending).

Integration branch: `ht/batch12` (to be cut off `pe/batch11` once PE stubs land). Proof branches `ht/<topic>` base off it. Merges: `ht/batch12` → local `main` after full close (never GitHub origin without user request).

## Design decisions (frozen)

- **Test primitive**: critical function `φ : 𝓧 → ℝ` with `IsCriticalFn φ := Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1`; `power P φ θ = ∫ φ ∂(P θ)` (ℝ-valued, finite for prob. measures); `IsLevel`, `IsMostPowerful`, `IsUMP`, `IsUnbiasedTest`, `IsUMPU`, `IsSimilar`, `HasNeymanStructure` predicates. Kernel bridge `randomizedTestKernel : Kernel 𝓧 (Fin 2)` defined fresh in ForMathlib (NOT promoting Minimaxity's private `binaryTest`).
- **Model carrier**: bare `P : Θ → Measure 𝓧` + `[∀ θ, IsProbabilityMeasure (P θ)]`; dominated statements via σ-finite μ + real densities with `P θ = μ.withDensity (ENNReal.ofReal ∘ p θ)`. NP thresholds in ℝ≥0∞ (k = ∞ corner real).
- **MLR**: division-free TP2 form `HasMLR p T := ∀ θ<θ', ∀ x y, T x ≤ T y → p θ' x * p θ y ≤ p θ x * p θ' y`.
- **Invariance**: `[Group G] [MulAction G 𝓧] [MeasurableSMul G 𝓧] [MulAction G Θ]` + `IsInvariantFamily (map_smul : (P θ).map (g•·) = P (g•θ))`; `IsMaximalInvariant`; almost-invariance ∀g ∀ᵐx. Finite-group orbit averaging `(card G)⁻¹ * ∑ g, φ (g•x)`.
- **Randomization (Ch 17)**: `RandomizationHypothesis P := ∀ g, P.map (g•·) = P`; `randDist` = (17.9); test via `MultipleTesting.orderStat` + M⁺/M⁰/a(x) trichotomy; exactness from the pointwise identity Σ_g randTest(g•x) = Mα.
- **Bootstrap (Ch 18)**: sequence-class C_P formulation (book-faithful, NO metric on measures); sampling-CDF field `J : ℕ → Measure 𝓧 → ℝ → ℝ` supplied as data; empirical measure a.s.-∈-C_P hypotheses; Kolmogorov sup-distance on CDFs; `levyProkhorovDist` for ℝ^k roots. Thm 18.3.2 via uniform-over-compact-h subsequence argument instead of Skorokhod (documented deviation).
- **Noncentral χ²**: `(multivariateGaussian (√λ•e₀) 1).map (‖·‖²)`; λ=0 bridge to `MultipleTesting.chiSquared`; tail monotone via Anderson.
- **KS calibration decision**: DKW-type fixed threshold (book's (16.8) discussion) — avoids the Kolmogorov limit law; constants non-sharp per charter; requires new `DKWUniform` brick (chaining + McDiarmid).
- **Ch 4 core**: `CondDistribTilt` ForMathlib brick (condDistrib of withDensity-tilted measure, standard Borel) — the book's Lemma 2.7.2 analogue; measurable C(t),γ(t) via condCDF patterns.
- **Lindeberg CLT**: new ForMathlib brick via charFun + Lévy continuity (serves 16.3.1, 17.2.4, 17.3.1, 18.3.3). Two-sample permutation CLT 17.3.1 = conditioning on weights + weighted-iid CLT + Cramér–Wold (verified book route; NOT Hoeffding combinatorial CLT).

## Named deferrals (pre-agreed, statement + named sorry, ledgered)

- Thm 18.4.1 / Thm 18.4.2 Edgeworth expansions (book cites Hall 1992, no proof).
- Lem 16.4.1 Bentkus-type multivariate Berry–Esseen (book cites Bentkus 2003, no proof); Thm 16.4.2 closes 0-sorry modulo it.
- Conditional fallbacks (only if the primary route stalls; see hotspots): generalized-NP general-m existence; 17.2.3(ii) converse's 2-D-CDF⇒weak brick; Lem 6.10.1's completeness sub-lemma; abstract mixture-NP-limit lemma of the maximin transfer.

## Work items (17) — 3 concurrent rolling waves

| id | wave | diff | headliners | prereqs (proof-level) |
|---|---|---|---|---|
| ht/test-foundations | 1 | L | NP lemma 3.2.1+Cor, 3.3.1, 3.5.1, 3.8.1+Cor | — |
| ht/lindeberg-clt | 1 | L | Lindeberg CLT, weighted-iid CLT, WLLN, Polya | — |
| ht/invariance-core | 1 | M | 6.1.1, 6.2.1, 6.2.2, 6.3.1, 6.3.2, 6.11.1 | — |
| ht/mlr | 2 | L | 3.4.1+Cor, 3.4.2, Lems 3.4.1/3.4.2, Cor 3.5.1 | test-foundations; pe exp-family MERGED (Cor only) |
| ht/generalized-np | 2 | XL | 3.6.1+Cor+Lem, 3.7.1+Lem | test-foundations; pe exp family MERGED (3.7.1) |
| ht/randomization-exact | 2 | M | 17.2.1, (17.2), (17.6), 17.2.2 | invariance defs (stub) |
| ht/unbiased | 3 | XL | 4.1.1, 4.3.2, 4.4.1 φ₁–φ₄, Lem 4.4.1 | pe completeness+sufficiency MERGED; generalized-np; mlr |
| ht/almost-invariance | 3 | L | 6.5.1+Cor+Lem, 6.5.2, 6.5.3, 6.6.1, 6.10.1 | pe bounded-completeness MERGED; invariance-core |
| ht/randomization-asymptotics | 3 | L | 17.2.3, 17.2.4, 17.3.2 | lindeberg-clt; test-foundations (quantiles) |
| ht/likelihood-trinity | 4 | L | 14.4.1, Cor 14.4.1, UniformLAN, 14.4.2 | AsymptoticStatistics assets (read-only) |
| ht/permutation-two-sample | 4 | XL | 17.3.1, 17.3.3, 17.4.1–3 | lindeberg-clt; randomization-asymptotics |
| ht/ks-dkw | 4 | L | DKWUniform, 16.2.1–16.2.3, (16.8) | CI McDiarmid (merged) |
| ht/noncentral-chisq | 4/5 | M | def + invariance + bridge + tail monotone | Anderson assets (read-only) |
| ht/chisq-multinomial | 5 | L | 16.3.1, 16.4.2, 16.4.1 (stmt+deferral) | lindeberg-clt; noncentral-chisq; pe exp family MERGED |
| ht/asymptotic-maximin | 5 | XL | maximin transfer, 16.3.2, Lem 16.3.1, 16.4.1 | LAN/contiguity; noncentral-chisq; NP |
| ht/bootstrap-core | 5 | L | 18.3.1, Lem 18.3.1, 18.3.3, 18.3.4 | lindeberg-clt; quantiles+Polya; DKWUniform |
| ht/bootstrap-advanced | 6 | L | 18.3.2, Cor 18.3.1, 18.3.5, 18.3.6, 18.4.x stmts, 18.5.1 | bootstrap-core; likelihood-trinity |
| ht/admissibility | 6 | L | 6.7.1+Cor, 6.7.2, Lem 6.7.1 | pe exp family MERGED; NP uniqueness; Bayesian NormalNormal (read-only) |

(ht/bootstrap-advanced ∥ ht/admissibility share wave 6 with a free 3rd slot for spillover.)

## Reuse map

pe (Batch 11): exp-family canonical form/log-partition/full-rank completeness (Thm 4.3.1 = pe statement, imported), bounded completeness, kernel sufficiency/factorization. AsymptoticStatistics: Contiguity/WeakConverges/Le Cam third, LANExpansion/AsymptoticRepresentation/productMeasure, ScoreCLT.clt_finDim, MultivariateCLT, CramerWold, Slutsky/SlutskyVec, Anderson, PrekopaLeindler, MultivariateGaussianSmul/Conv, LogTaylor. MultipleTesting: empiricalCDF, chiSquared + map_sum_sq_eq_chiSquared + mgf, orderStat, SuperUniform, SymmetricCondExp. ConcentrationInequalities: McDiarmid, markov. Bayesian: NormalNormal (Lem 6.7.1). Minimaxity: tvDist view optional.

## Statement-first stub phase — COMPLETE (2026-07-18)

63 files, 243 sorry-stubs, drafted by an 8-agent fan-out, all committed on `ht/batch12`
(which now also carries a merge of the full `pe/batch11` tree).

| Directory | Files | Stubs |
|---|---|---|
| ForMathlib | 10 | 54 |
| Tests | 3 | 10 |
| MLR | 5 | 16 |
| NeymanPearson | 3 | 17 |
| Invariance | 10 | 35 |
| Unbiased | 5 | 18 |
| LikelihoodMethods | 4 | 10 |
| GoodnessOfFit | 7 | 26 |
| Randomization | 9 | 31 |
| Bootstrap | 7 | 26 |

### Honest corrections to the source and to the drafting briefs

Errors found in the reference text itself:
- **Thm 17.3.2's parenthetical `R^{aT+b}(t) = R^T((t−b)/a)` "for a ≠ 0" is false for `a < 0`.**
  `cdf_map_affine` is stated for `0 < a`.
- **Thm 18.5.1 needs strict increase at the quantile**, not just continuity of `G(·,P)`: a flat
  stretch at height `1 − α` leaves the quantile undetermined. Made explicit (the source does state
  it in 18.3.1).
- **Thm 18.3.5's class must include mean-vector convergence** — the source lists only weak +
  covariance convergence, but its own Cramér–Wold reduction to 18.3.3(i) consumes the means.
- **Thm 18.3.2 needs tightness of `√n(θ̂ₙ − θ)`, not mere consistency**: consistency alone never
  activates a compact-`h` hypothesis.
- **No integrality caveat exists** in the randomization identity (17.2): `∑_g φ(g·x) = Mα` holds
  exactly for every `x`; `a(x)` absorbs the fractional part. What `0 < α < 1` actually buys is
  `k ∈ {1,…,M}` (keeping the critical value off the junk branch) and `M⁰ ≥ 1` (no `0/0`).

Anti-laundering corrections:
- Thm 17.2.4's `E_P[ψ(X)] = 0` is FORCED by "ψ odd" + "P symmetric" + square-integrability;
  carrying it would be laundering. Dropped; `0 < τ` added as an explicit LEAN-ONLY nondegeneracy.
- `CondDistribTilt`'s normalizer positivity/finiteness are DERIVED, not hypothesized.
- Cor 18.3.1's `hlocalCLT`/`hcritval` are flagged as belonging to the local-asymptotics layer —
  to be discharged there, not by callers.
- Thm 6.5.1 needs `ν ≠ 0` (the source says "w.l.o.g. ν(G) = 1", impossible for the zero measure).

Brief errors caught by the agents (page/label mistakes in my own instructions):
- The measurable-factorization hypothesis for Thm 6.2.1 is at PDF **267**, not 257.
- Displays (16.28)–(16.30) are at PDF **796–797**, not 806–807 (which is the smooth-test material).
- **Thms 18.4.1/18.4.2 labels were swapped** in the brief: 18.4.1 is the NON-studentized root
  (`EX⁴ < ∞` + Cramér), 18.4.2 the studentized one (`EX⁴ < ∞` + absolute continuity).
- My `(18.17)` pointer is Cramér's condition in this edition; the 18.3.1 coverage display is (18.6).
- Thm 17.3.3's "equivalence with the two-sample t-test" is the EQUAL-variance pooled-t remark; the
  honest unequal-variance statement is that the studentized statistic is algebraically the
  **Welch** t-statistic, so the level result transfers verbatim. Stated that way.

Design/route decisions:
- **DKW constants `4·exp(−d²/8)`** (not the briefed `1/2` exponent): with mean bound `E[√n Dₙ] ≤ 2`,
  McDiarmid only covers `d ≥ 2`, and `4e^{−d²/2}` drops below 1 at `d ≈ 1.66`, leaving a gap.
  `4e^{−d²/8}` satisfies `2(d−2)² ≥ d²/8 − log 4` for all `d ≥ 2` (min slack ≈ 0.85). Both are
  implied by sharp Massart. Consequence: `ksThreshold α = √(8·log(4/α))`, the single coupling
  numeral between `DKWUniform` and `GoodnessOfFit/KSConsistency`.
- DKW calibration makes Thm 16.2.3 **exact** rather than slack, and needs **no continuity of F₀**
  (unlike quantile calibration).
- §17.4's three lemmas use the **sign-change** group, not permutations.
- `randomizedTestKernel` is defined fresh (not a promotion of Minimaxity's private `binaryTest`).
- `groupAverage` (ForMathlib) vs `orbitAverage` (Invariance/Defs) kept distinct to avoid a
  namespace collision; `Randomization/OrbitConditional` has its own `invariantSigmaAlgebra`.
  **Dedupe candidates for the laptop session** (all three pairs are same-namespace duplicates):
  `groupAverage`/`orbitAverage`, `quantile`/`cdfPseudoInverse`, `empCDF`/`empiricalCDF`.
- Thm 6.3.1's orbit average: the source averages *translated parameter densities*, the frozen
  `orbitAverage` averages *over the sample*; these agree only when the dominating measure is
  `G`-invariant. Headline is stated sample-side plus an explicit bridge lemma carrying that
  invariance hypothesis.
- Bentkus is stated in the **ball** form (not the `400k^{1/4}` convex form): the convex constant
  would force `kₙ^{7/2}/n → 0` rather than the needed `kₙ³/n → 0`.

## Event log

- 2026-07-15: design frozen (17 items, 6 waves); stubs pending.
- 2026-07-18: weekly-quota interruption killed the first fan-out; relaunched.
- 2026-07-18: stub phase COMPLETE — 63 files / 243 stubs committed; `pe/batch11` merged in; full-tree stub gate running.
