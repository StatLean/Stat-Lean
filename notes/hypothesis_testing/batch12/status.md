# HypothesisTesting Batch 12 — orchestration status

Last update: 2026-07-27 (HT 28 after wave-2: all 7 lanes merged — Bootstrap/Multivariate, ChiSquaredMultinomial, Randomization/Asymptotics+Slutsky, SymmetryIdentity 0-sorry; ConfidenceBounds+SymmetryIdentity+MultiparamUMPU inside/outside REPAIRED+PROVED; triangular_wlln repaired. Wave-3 launched on the last 28).
Integration branch: `ht/batch12` (to be cut off `pe/batch11` once PE stubs land). Proof branches `ht/<topic>` base off it. Merges: `ht/batch12` → local `main` after full close (never GitHub origin without user request).

## Current state — 2026-07-25

**Area gate: GREEN.** `lean-fasrc-build --worktree ht/batch12 StatLean.HypothesisTesting` →
`Build completed successfully (3287 jobs)`, exit 0. Build-reported sorry-uses **112**; literal
`grep` count **118** (the two differ because some sorries sit in unreachable/private branches).
Integration branch tip `cd1ae5b`. Both counts are down from the 2026-07-20 baseline of 121.

**Open sorries (118 literal), distributed as:**

| count | file |
|---|---|
| 7 | ForMathlib/TestsWeakCompact.lean |
| 7 | Bootstrap/Multivariate.lean |
| 6 | Unbiased/MultiparamUMPU.lean |
| 6 | **ForMathlib/MultivariateBerryEsseen.lean** (NEW brick; 6 named ball-route debts) |
| 6 | Bootstrap/NonparametricMean.lean |
| 5 | LikelihoodMethods/TrinityChiSquared.lean |
| 5 | GoodnessOfFit/ChiSquaredMaximin.lean |
| 4 | Randomization/MultivariateQuadratic.lean, NeymanPearson/Generalized.lean, MLR/TwoSided.lean |
| 3 | Randomization/{TwoSamplePermutation,Studentized,SignChange}, MLR/OneSided, LikelihoodMethods/EstimatorUnderAlternatives, Invariance/Admissibility, GoodnessOfFit/SmoothTestLargeK, Bootstrap/Edgeworth |
| 2 | Unbiased/{OneParamTwoSided,ConditionalExpFamily}, NeymanPearson/Lemma, MLR/StochasticDominance, Invariance/{SymmetryIdentity,AlmostInvariance}, GoodnessOfFit/{SmoothTest,KSConsistency,ChiSquaredMultinomial}, ForMathlib/{DKWUniform,CondDistribTilt}, Bootstrap/ParametricLocal |
| 1 | 13 further files |

Note `Invariance/BayesAdmissible.lean` and `ForMathlib/BerryEsseen.lean` are absent from the list
(both 0-sorry), and `ForMathlib/NoncentralChiSquared.lean` dropped 4→1 — see below.

### Closed / added since 2026-07-20

- **`Invariance/BayesAdmissible.lean` → 0-sorry** (was 4). thm4 `bayesTest_isDAdmissible`
  (axiom-clean; Bayes-risk vanishing-objective + `k≥0`/`k<0` mutual-a.c. split), thm5
  `bayesTest_isAlphaAdmissible` (via `bayes_admissible_core`), thm6 `bayesTest_admissible_of_subset`,
  thm7 `exists_gaussian_scale_mixture` (axiom-clean; density-uniqueness reusing `comp_gaussKernel`).
- **`ForMathlib/NoncentralChiSquared.lean` 4→1.** Targets A/B/C closed:
  A `weakConverges_chiSquared_standardized` (`(χ²_k−k)/√(2k) ⟹ N(0,1)` via
  `map_sum_sq_eq_chiSquared` + `weighted_iid_clt` at `w≡1, Y=Z²−1, σ=√2`, so `σ√(∑w²)=√(2k)`
  makes the CLT statistic literally the target); B `tendsto_chiSquared_quantile_standardized`
  (portmanteau on open half-lines); C `weakConverges_noncentralChiSquared_standardized`
  (Slutsky on A). D `noncentralChiSquared_tail_mono` reduced to a lifted Anderson lemma (open).
  **This unblocks the two lifted `AsymptoticMaximin` theorems + the `ChiSquaredMaximin` chain**
  (staged lane `ht/maximin-3b`).
- **`ForMathlib/BerryEsseen.lean` — NEW, 0-sorry, axiom-clean.** The characteristic-function
  half of Berry–Esseen: `norm_charFun_sub_quadratic_le`, `norm_charFun_pow_sub_gaussian_le`,
  `norm_charFun_iidSum_sub_gaussian_le` — a complete explicit `O(1/√n)` charFun bound. Restates
  `LindebergCLT`'s private Taylor/product bounds (they cannot be imported). Fejér-kernel
  foundations laid but the CDF-level Esseen smoothing inequality is NOT included (blocked — see
  Edgeworth below).
- **`ForMathlib/MultivariateBerryEsseen.lean` — NEW.** `gaussian_slab_measure_le` (dimension-free
  slab anti-concentration, const `1/√(2π)`, no `k`-factor, axiom-clean) + `norm_taylor_remainder_three_le`
  (3rd-order Taylor on a normed space — fills a genuine Mathlib gap, only 1-D existed) +
  Step-1 ball reduction (Gaussian shell mass = `chiSquared` interval mass). 6 named ball-route
  debts remain (`exists_smoothed_radial_indicator`, the Lindeberg swap, `berryEsseen_ball_elementary`,
  the convex case); staged lane `ht/bentkus-3` finishes them.
- **`ForMathlib/CondDistribTilt.lean` Target 1** `measurable_condTiltNormalizer` merged.
  Targets 2 & 3 (`condTiltNormalizer_pos_lt_top_ae`, `condDistrib_fst_withDensity_tilt`) staged
  (`ht/condtilt-2`); a prior attempt's quota-killed auto-close was a BROKEN mid-edit (build
  errors at lines 151 + 304) and was reverted — do NOT trust its "0-sorry" grep. Closing these
  2 unblocks the 6 in `Unbiased/MultiparamUMPU.lean`.
- **`Randomization/SignChange.lean`** — `hT : ∀ n, Measurable (T n)` added to all 4 signatures
  (thm1 `weakConverges_randPairLaw_signChange` was proven **FALSE as stated** without it — a
  Bernstein-set statistic makes every `randPairLaw` the zero measure while `hlin` holds, since
  `TendstoInProbTriangular` uses outer measure). thm2 `randDist_signChange_tendstoInProb` now
  CLOSED; thm3/thm4 staged (`ht/signchange-4`); thm1 needs a bivariate CLT (hard, may stay debt).
- `GoodnessOfFit/AsymptoticMaximin.sphereAverage_lr_monotone` — axiom-clean (reflection isometry
  + `cosh` monotonicity, no Bessel theory).

### CORRECTION to the 2026-07-20 "structural blocker" claim
The earlier note said ~21 sorries (TestsWeakCompact, MultiparamUMPU, NP/Generalized, MLR/TwoSided)
all reduce to missing `L^∞ ≅ (L¹)*`. **That was overstated.** Re-reading the files: only
`NeymanPearson/Generalized.isClosed_momentSet` (1 sorry) genuinely needs it — and **even that
dissolves** via a change of measure into `L²` (dominate the `m` constraint functions by a weight
`w=(∑|fᵢ|+h)/Z`, push the `[0,1]` test class into `L²(ν=wμ)`, use Hilbert self-duality which
Mathlib HAS). `TestsWeakCompact` is deliberately stated in `L²` over a finite measure to avoid
the duality (needs only Fréchet–Riesz + Banach–Alaoglu); `MultiparamUMPU` blocks on `CondDistribTilt`
+ measurable selection; `MLR/TwoSided` has no duality reference. Full write-up + the ball-vs-convex
Route-A/B analysis in the conversation's `informal-L1-duality.md`; the momentset+TestsWeakCompact
close is staged (`ht/momentset-l2`, 8 sorries). The standalone `L^∞ ≅ (L¹)*` theorem was
explored (all Radon–Nikodym/simple-function ingredients verified present in Mathlib) then dropped
per user instruction as unnecessary for any consumer.

### Sanctioned deferrals — status
- **Edgeworth 18.4.1/18.4.2** (`Bootstrap/Edgeworth.lean`, 3 sorries): **recommend permanent
  deferral.** Verified they have ZERO downstream consumers (nothing imports the file's decls).
  The CDF-level Esseen smoothing inequality they need is blocked on THREE separately-absent
  Mathlib foundations: the sinc integral `∫(sin x/x)²=π` (and Dirichlet `∫ sin x/x=π/2` — Mathlib
  has neither), the Fejér-kernel Fourier transform, and a Stieltjes/CDF-level Lévy inversion
  (`Integrable.fourier_inversion` is `L¹`-only). The charFun *half* is done and banked in
  `ForMathlib/BerryEsseen.lean`.
- **Bentkus multivariate Berry–Esseen** (`GoodnessOfFit/SmoothTestLargeK.lean`,
  `bentkus_berry_esseen_{convex,ball}`): the sharp `400·k^{1/4}` convex bound stays deferred
  (needs Bentkus 2003's Gaussian-surface-area bound). BUT the **ball** case is attackable by the
  elementary mollifier route, which yields rate `(β/√n)^{1/4}` — worse than the book's `β/√n`,
  intrinsic to the method, but the consumer `smoothStat_largeK_weakConverges_gaussian` **still
  closes under the book's own `kₙ³/n→0`** because `(k^{3/2}/√n)^{1/4}→0 ⟺ k³/n→0`. So amend the
  frozen `bentkus_berry_esseen_ball` to the honest `(β/√n)^{1/4}` form (documented deviation)
  and close the consumer — staged (`ht/bentkus-3`).

### Statement amendments made during closure (all verified necessary)
- `Randomization/Asymptotics.lean` — `randDist_tendstoInProb_cdf` / `randQuantile_tendstoInProb`
  gained `hT : ∀ n, Measurable (T n)` + a measurable-action hyp (zero-measure degeneracy without it).
- `Randomization/SignChange.lean` — `hT` on all 4 signatures (thm1 false without it; see above).
- `MLR/OneSided.lean` — `hα : α ∈ Icc 0 1` → `Ioo 0 1` (Icc form FALSE at endpoints, 4
  counterexamples); `isUMP_oneSided_shifted` gained `hz : ∃ z, C ≤ T z ∧ 0 < p θ' z`.
- `Bootstrap/Consistency.lean` — `supCDFDist_triangle` → `supCDFDist_triangle_of_isCDF` (collision).
- (planned) `GoodnessOfFit/SmoothTestLargeK.bentkus_berry_esseen_ball` → honest `(β/√n)^{1/4}` rate.

### Infra
- `.gitignore` now excludes `.fanout-prompt.md` + `.claude-session.log` (the fan-out launcher
  writes these into each worktree and its auto-close `git add -A` was committing them onto every
  harvested branch). Fixed 2026-07-25.
- **Cluster campaign paused 2026-07-25:** FAS-RC account saturated by an unrelated `radon11-*`
  job workflow (cycles 15↔140 jobs, ~90 running at peak; drives login load to ~43). srun blocked
  on all normal partitions; `bigmem_intermediate` needs >1000GB/node; login-node `SRUN=0` claude
  hangs at startup. Staged lanes (`condtilt-2`, `maximin-3b`, `bentkus-3`, `bootmean`, `momentset-l2`,
  `signchange-4`) are ready to fire the instant serial_requeue has room.

## Re-test wave — 2026-07-26 (area gate GREEN, 3304 jobs, 76 sorry-uses)

**HT 88 -> 77.** The cluster env had `ANTHROPIC_MODEL=claude-opus-4-8` pinned for the whole
earlier campaign. After switching to `claude-opus-5`, the three targets that 4.8 had
documented as *genuinely blocked on absent Mathlib infrastructure* were re-run with prompts
that explicitly declared the earlier verdicts unreliable. **All three verdicts were wrong.**

* **`ht/retest-umpu`** — 4.8 said the UMPU chain was blocked on "a Xi-Borel measurability
  gap". Reality: `Unbiased/ConditionalExpFamily.lean` -> **0-sorry**
  (`condDistrib_expFamily_of_isCanonicalUT`, `condDistrib_eq_of_fst_eq`), plus
  `exists_measurable_conditional_constants` and `isCanonicalUT_reparam` closed in
  `MultiparamUMPU`; and the **four conditional-UMPU statements are FALSE**, shown by a
  formalized counterexample.
* **`ht/retest-boot`** — 4.8 said all 7 `Bootstrap/Multivariate` sorries needed "a
  triangular-array multivariate CLT + delta-method infra not present". Reality: 14 commits
  closing `meanVec_root_tendsto` (Cramer-Wold onto the drifting-row CLT),
  `mean_root_cdf_tendsto` (CDF->weak bridge + array CLT + portmanteau),
  `empirical_mem_meanVecSeqClass` (SLLN + Levy) and `bootstrap_meanVec_consistent` —
  **TSH Thm 18.3.5 complete** — plus charFun-equicontinuity and empirical-measure bricks.
* **`ht/retest-trinity`** — closed `measurable_logLRStatistic` (forced joint-measurability
  amendment), `wald_sub_score_tendstoInMeasure`, and `affineScoreDiff_tendsto_chiSquared`
  (rank-p Gaussian projection bridge); and `sup_LAN_remainder_tendsto` is **FALSE as stated**,
  counterexample recorded.

### Methodological conclusion
Nine theorems that opus-4.8 documented as impossible or unprovable have now been proved, and
the re-tests additionally produced five FALSE-as-stated counterexamples. **Any remaining
blocked-verdict in this area that predates the opus-5 switch should be treated as unverified
until re-derived.** Model-attributed impossibility is not evidence of impossibility.

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
- 2026-07-18: stub phase COMPLETE — 63 files / 243 stubs committed; `pe/batch11` merged in.
- 2026-07-18: **FULL-AREA GATE GREEN — `lake build StatLean.HypothesisTesting`: 0 errors,
  243 sorries, `Build completed successfully`.** Took four rounds; the fixes were all
  mechanical, not mathematical:
  1. `ℙ` used as a `variable` binder in five Bootstrap files — `ℙ` is notation, not a legal
     identifier; the broken `variable` block cascaded into 48 downstream unknown-identifier
     errors (65 → 17 by renaming to `Pr`).
  2. `ḡ` (U+1E21) as an identifier in `Invariance/MaximalInvariant` — precomposed Latin
     Extended Additional is outside Lean's identifier alphabet. Renamed to `gbar`. (The same
     glyph inside docstrings elsewhere is harmless.)
  3. Numeric-coercion binders: `fun n => … Real.sqrt n …` retypes `n` to `ℝ`, breaking
     `Fin n` / `F n` / `Y n` downstream. Fixed by annotating `fun n : ℕ =>` in
     `KSLocalPower`, `LindebergCLT`, `Bootstrap/{Consistency,NonparametricMean}`.
  4. `ProbabilityMeasure ℝ` built by anonymous constructor loses its topology instance —
     restated row-law weak convergence in portmanteau form (`∀ f : ℝ →ᵇ ℝ, …`), matching
     `AsymptoticStatistics/ForMathlib/Contiguity.lean`'s own `WeakConverges`.
  5. `if T (g • x) ∈ B then …` needs `Decidable` for an arbitrary set — used `Set.indicator`.
  6. `cov[fun y => WithLp.ofLp y i, …]` — the lambda binder's type does not infer through the
     covariance notation; annotated.
  Area umbrella `StatLean/HypothesisTesting.lean` created (laptop-only surface).

## Proof-closure phase — findings (2026-07-19)

### FALSE STATEMENT found and FIXED: instance capture in `condExp_eq_groupAverage`

The `ht/invariance-core` session refused to close it and gave a complete counterexample.
The frozen signature was

```
theorem condExp_eq_groupAverage (m : MeasurableSpace 𝓧)
    (hm_inv : ∀ s, MeasurableSet[m] s ↔ s ∈ invariantSets G 𝓧) …
```

`invariantSets G 𝓧` takes `[MeasurableSpace 𝓧]` as an *instance*, and Lean's local-instance
resolution picks the most recent local hypothesis — the explicit parameter `m` — not the
ambient `m𝓧`. So `hm_inv` elaborated to
`MeasurableSet[m] s ↔ (MeasurableSet[m] s ∧ IsInvariantSet G s)`, i.e. merely "every
`m`-measurable set is invariant". It did **not** force `m ≤ m𝓧`, which
`ae_eq_condExp_of_forall_setIntegral_eq` requires.

**Counterexample**: `𝓧 = ℝ`, `G = ℤ/2` acting by `x ↦ −x`, `μ` = standard Gaussian
(`G`-invariant), `m = {∅, ℝ, N, Nᶜ}` with `N` a non-Lebesgue-measurable symmetric set. Then
`hm_inv` holds, `m ⊄ m𝓧`, so `μ[f|m] = 0` while `groupAverage G f x = (f x + f (−x))/2 ≢ 0`.

**Fix applied (laptop):** pin the ambient instance — `s ∈ @invariantSets G 𝓧 _ m𝓧 _`. Under
that reading the statement is true and the intended proof works.

**Generalizable lesson:** any statement that takes a `MeasurableSpace` (or any other class) as
an *explicit* parameter while also relying on the ambient instance is at risk of silent
capture. Audit the other places where a σ-algebra is passed explicitly.

### Other results

| item | outcome |
|---|---|
| `ht/test-foundations` | Critical functions, quantiles (**incl. the randomization-constant existence lemma**), p-value super-uniformity, and **all six confidence-duality theorems** closed. NP existence/necessity + least-favorable left for a second pass. |
| `ht/mlr-np2` | **NP existence (`exists_mostPowerful`) closed**, `hasMLR_expFamily` closed, `integral_mono_of_hasMLR` closed. |
| `ht/invariance-core` | Group averaging 8/9, maximal invariants 7/11, orbit-average invariance, equivariant-confidence dictionary. 4 `MaximalInvariant` statements reported **under-hypothesized** (missing measurability) — needs a signature review like the one above. |

## Proof-closure scoreboard (2026-07-19) — HT sorry count **243 → 165 (32% closed)**

**Fully closed files:** `ForMathlib/{CriticalFunction,QuantileFunction,GroupAverageMeasure,
HypergeometricMoments}`, `Tests/{PValue,Confidence}`, `Randomization/{ExactLevel,
OrbitConditional}`, `Invariance/UMPInvariantFinite`.

**Headline theorems proven:** the Neyman–Pearson randomization-constant existence lemma (the
single most reused result in the chapter); NP existence (`exists_mostPowerful`) and the
sufficiency direction; p-value super-uniformity (Lem 3.3.1); **all six test↔confidence duality
theorems (Thm 3.5.1)**; exponential-family MLR and monotone expectations; **exact finite-sample
level of the randomization test (Thm 17.2.1)** together with the orbit-conditional law
(Thm 17.2.2) and the randomization p-value; the conditional-expectation/orbit-average identity;
**the UMP invariant test for finite groups (Thm 6.3.1)** and its two supporting theorems;
boundary similarity and the UMPU criterion (Lem 4.1.1); bounded completeness ⇒ Neyman structure;
`InducesOn` group laws; the triangular-array **Lindeberg CLT** and its bounded corollary, resting
on a uniform third-order remainder bound for `exp(iy)` that had to be built because Mathlib
provides only a non-uniform `o(t²)` version.

## Statement defects found and FIXED

1. **`condExp_eq_groupAverage` was FALSE — Lean instance capture.** The explicit
   `(m : MeasurableSpace 𝓧)` shadowed the ambient instance inside `invariantSets` in `hm_inv`,
   so the hypothesis said only "every `m`-measurable set is invariant" and never forced
   `m ≤ m𝓧`. Counterexample: `ℝ` with `ℤ/2` acting by reflection, standard Gaussian, `m`
   generated by a non-measurable symmetric set. **Fixed** by pinning the ambient instance
   (`@invariantSets G 𝓧 _ m𝓧 _`); the theorem then closed axiom-clean.
   *Generalizable:* any statement passing a typeclass explicitly while also relying on the
   ambient instance is at risk of silent capture. Worth auditing elsewhere.
2. **`isUMPInvariant_of_orbitAverage_ratio` was FALSE** without invariance of the dominating
   measure. Counterexample: `ℤ/2` reflection on `ℝ`, every `P θ` symmetric so
   `IsInvariantModel` holds, but `μ = N(1,10)` asymmetric makes the sample-side orbit-average
   ratio differ from the likelihood ratio — invariant but not UMP. **The tell:** the theorem's
   own proof sketch invoked invariance of `μ` for a hypothesis absent from its signature.
   **Fixed**; all three `UMPInvariantFinite` theorems then closed.
3. **`orbitAverage_eq_avg_translated_density` was under-hypothesized** — extracting a.e.
   equality of density *functions* from equality of `withDensity` *measures* needs
   `[SigmaFinite μ]`. **Fixed.**
4. **`InducesOn.mul` / `.inv` were under-hypothesized** — `Measure.map_map` splits a composite
   pushforward and needs *both* factors measurable; inverting needs both directions. **Fixed**;
   both then closed.
5. Six stub-gate defects (identifier legality `ℙ`/`ḡ`, numeric-coercion binders,
   `ProbabilityMeasure` topology loss, decidability, `ofLp` elaboration) — all fixed earlier.

## Genuine obstructions (not signature gaps)

- `isInvariantTest_iff_factors_measurable` (⇒): needs **measurable uniformization**
  (Jankov–von Neumann); from a bare `MeasurableEmbedding` the factor's sublevel set is an
  analytic projection, not measurable. Documented, not attempted.
- `isUMAEquivariant_of_isUMPInvariant`: competitors are quantified without measurable slices,
  and it waits on `power_acceptanceTest` in `Tests/Confidence`.
- Edgeworth (Thms 18.4.1/18.4.2) and the Bentkus bound (Lem 16.4.1): **proofless in the source**;
  pre-agreed statement-plus-deferral.

### VERIFIED integration gate (2026-07-19)

`lake build StatLean.HypothesisTesting` on the cluster: **0 errors, `Build completed successfully`,
164 sorried declarations** (down from 243 at the stub gate — **33% closed**). The build warning
count is authoritative; `grep -c sorry` reports 165 (docstring/TODO mentions).

### Wave tallies (2026-07-27, Opus 5 era)

Progression of the authoritative build-warning sorry count on `ht/batch12`:
**122 → 88** (re-tests) → **77** (re-test wave 2) → **43** (final-closure 9-lane) → **28** (wave-2,
7-lane) → **23** (wave-3, 5-lane) → **16** (wave-4, 5-lane; gate green, tip `de3656b`).

Wave-4 headliners (all axiom-clean):
- `asymptotic_maximin_upper_bound` CLOSED — Cameron–Martin sphere-averaged likelihood-ratio
  transfer lemma, generalised to varying sample spaces and an eventual shell (`AsymptoticMaximin`
  now 0-sorry).
- `dkw_uniform` CLOSED at the provable constants `4 e^{-d²/16}` (documented deviation from the
  sharp `2 e^{-2d²}`; `ksThreshold` recalibrated to `√(16 log(4/α))`, KS consumers hold verbatim).
  `DKWUniform.lean` 0-sorry.
- `logLR_tendsto_chiSquared_affine` CLOSED (`TrinityChiSquared.lean` 0-sorry) — affine composite
  via two applications of the simple-null lemma; common-support-relative-to-θ₀ repair.
- MVQ sign-change headliners CLOSED (`MultivariateQuadratic.lean` 0-sorry): Hotelling `T²` and
  modified `T²` randomization laws.
- `weakConverges_studentizedTwoSample` CLOSED; damped one-term Edgeworth charFun expansion (G2)
  + Cramér tail input (E3) CLOSED (`ForMathlib/BerryEsseen.lean` 0-sorry).

Remaining 16: Edgeworth trio (proofless in source; deferral), `berryEsseen_convex_elementary`
(Ball's theorem; deferral), `weakConverges_randPairLaw_twoSample` (Hoeffding combinatorial CLT;
deferral candidate), and 11 reachable targets under wave-5 (lanes: Studentized assembly,
GoF shell/minPower chain + large-k consumer, MBE smoothed convex indicator, singles
TwoSided/MultiparamUMPU/EstimatorUnderAlternatives).

### Waves 5–11 (2026-07-27, Opus 5): 16 → 4

**16 → 4** across waves 5–11. Chapters now fully 0-sorry: **Randomization (TSH ch. 17) entire**,
Unbiased/MultiparamUMPU, GoodnessOfFit (except the quoted Bentkus reference statement),
LikelihoodMethods, MLR, and the `ForMathlib` layer except `MultivariateBerryEsseen`'s quoted
sharp bound.

Landmark closures (all axiom-clean):
- **The combinatorial central limit theorem** (`ForMathlib/CombinatorialCLT.tendsto_perm_cdf_blockSum`)
  — Wald–Wolfowitz/Noether/Hoeffding/Hájek. Two earlier sessions recorded this as unreachable
  ("no combinatorial CLT, no Stein machinery, no finite-population limit theorem in Mathlib").
  Built from scratch: `ForMathlib/SteinMethod` (Stein equation, abstract exchangeable-pair
  theorem, and the three classical solution bounds `‖f_h‖ ≤ L`, `‖f_h'‖ ≤ 2L`, `f_h'` 5L-Lipschitz),
  the permutation swap pair with its exact conditional variance, and the Lindeberg-scale
  truncation. A sharpened counterexample in the file records *why* the untruncated pair fails:
  its third-moment error term can diverge under the theorem's own hypotheses.
- **The Gaussian shell bound for convex sets** (`ForMathlib/GaussianShell.gaussian_thickening_le`),
  `γ(Bᵋ) ≤ γ(B) + C_k ε` with `C_k = 8k^{3/2}/√(2π)`, proved elementarily — no Ball's theorem, no
  Gaussian isoperimetry. Earlier notes deferred this as "Ball's Gaussian-surface-area theorem";
  that verdict was too strong, since the consumer quantifies over a *fixed* dimension and so
  needs only a dimension-dependent constant. It closed
  `MultivariateBerryEsseen.berryEsseen_convex_elementary`.
- `isUMPU_conditional_point` (TSH 4.4.1 conditional UMPU, point null), the two goodness-of-fit
  shell-attainment lemmas, `isUMP_twoSided` (under the documented `hatom` amendment),
  `weak_limit_estimator_under_local_alternatives` (under the common-support repair), the
  studentized permutation chain end to end, and Edgeworth (E1)–(E3) + (E4.1)/(E4.2).

**Remaining 4**, all documented deferrals or in flight:
1. `edgeworth_mean_uniform` — (E4.3) window integral + (E4.4) outer range; every analytic core
   is proved, the remainder is quantitative assembly. In flight.
2. `edgeworth_studentized_uniform` and 3. `cornishFisher_studentized_quantile` — need the
   **bivariate** Edgeworth expansion for `(X̄, X̄₂)` plus the delta-method transfer. The verdict
   was independently re-derived twice; it stands, with a proof that no Slutsky-type reduction to
   the centred root can work at any rate finer than `n^{-1/2}` (the two approximants differ by
   exactly `(1/2)γt²φ(t)n^{-1/2}`).
4. `bentkus_berry_esseen_convex` — quotes the **sharp** Bentkus 2003 rate `400 k^{1/4} β/√n`.
   **Zero consumers** repository-wide; the weakened convex statement at the elementary rate
   `C_k(β/√n)^{1/4}` is proved as `berryEsseen_convex_elementary`.

### Waves 13–24 (2026-07-28): the multivariate Berry–Esseen line reaches its honest boundary

Sequence of verdicts *overturned* on re-derivation, each by building the object the previous
note described: the Stieltjes-inversion obstruction (wave 3-era), "Ball's theorem is needed for
the Gaussian shell bound" (wave 10 — a dimension-*dependent* constant suffices, and
`gaussian_thickening_le` was proved elementarily), "the exponent 1/4 is intrinsic" (wave 13 —
the hybrid telescope's `j`-th step is already Gaussian-mollified, so a Cameron–Martin tilt
replaces the mollifier's `ε^{-3}` by `ε^{-1}`), and "Bentkus's induction is not attempted"
(waves 19–20 — the scalar fixed points and then the recursion itself were produced).

**Proved and axiom-clean now:** `berryEsseen_convex_improved` and `berryEsseen_ball_improved`
at `(β/√n)^{1/2}`; the whole Cameron–Martin apparatus including the weighted (Hölder/`L²`)
remainder; the hybrid telescope; the self-improving recursion over the convex-discrepancy class
and the hybrid family; brick H `hybridLaw_shell_le`; and the Gaussian shell constant improved
from `k^{3/2}` to **`√k`**.

**The boundary.** Wave 24 found brick L FALSE as frozen — witness `k = 1`, `n = 1`, `ν` the
two-point law with mass `p` at `−a`, `a = √((1−p)/p)`, `B = (−∞, −a/2]`: the shell misses both
atoms, so the bare weight `W ≍ e^{−a²/8}` is admissible while the discrepancy is `≍ p`. The
minimal amendment (weight `W + C_k ε`, free at the only call site) is applied, and the
large-weight half is proved (`exists_smooth_swap_bound_of_one_le_weight`). What remains,
`localised_swap_bound_small_weight`, is *"a Gaussian surface-area statement about convex bodies
— the same input as Ball's"*. And the same input is what separates the route's `√k` from the
book's `400 k^{1/4}` in `bentkus_berry_esseen_convex`.

So **both** remaining Berry–Esseen items reduce to one research-level theorem (K. Ball,
*Gaussian surface area of convex bodies*), whose formalisation is a project in its own right.
This is recorded as the honest stopping point of this line, not as a verdict to be re-litigated:
unlike its predecessors it is a named external theorem, not a gap in the local argument.

---

## FINAL — 2026-08-03: BATCH 12 CLOSED at 0 sorries

**Area gate GREEN, sorry-uses-in-build-output: 0** (`lean-fasrc-build --worktree ht/batch12
StatLean.HypothesisTesting`, tip `536b270`). Source sweep: 0 `sorry`/`admit`/`axiom` across all
73 files. Umbrella `StatLean/HypothesisTesting.lean` imports all 73 modules (verified 1:1);
`StatLean.lean` wires the area (added at close-out, commit `3bae13f`).

**The 30-wave Berry–Esseen/Edgeworth endgame (waves 13–53).** The last five sorries required
~40 cluster lanes across three weeks. Outcomes:

* `ForMathlib/MultivariateBerryEsseen.lean` — **0-sorry since wave 43.** `berryEsseen_convex_sharp`
  fully proved at the honest amended rate `C·(β/√n)·(1 + log(√n/β))^{3/2}`, `C ≍ k`
  (deviations from Bentkus's log-free `k^{1/4}` documented in-file; the gap to the sharp constant
  is Ball's Gaussian-surface-area theorem, a recorded note, not a debt). Key final bricks: head
  estimate (w38), sub-Gaussian norm tail + (1+log)^{3/2} fixed-point re-solve (w39), third-moment
  far regime (w40), tail brick via tilt export + varying-width Fubini (w41), deconvolution
  transfer (w42, after w41's transfer was refuted with a witness), √k-window threading + final
  assembly (w43).
* `Bootstrap/Edgeworth.lean` — **0-sorry after a user-authorized removal (2026-08-03).**
  `edgeworth_mean_uniform` (the centred-root expansion) is PROVED. The studentized headline
  `edgeworth_studentized_uniform` and its corollary `cornishFisher_studentized_quantile` were
  REMOVED with in-file removal notes: waves 44–53 proved every ingredient (certificate at the
  repaired band `K√(log n)`/N=10 with inputs (A),(B),(C) all closed — (B) at fourteen parts;
  the middle-range theorem; the (U3) anti-concentration chain; the iid moment recursion with
  Rosenthal at orders 6–10; the affine transfer (an equality); the skewness comparison; the
  four-slot Esseen ledger, each slot O(1/n)) but the final composition was never assembled; the
  wave-53 notes record the residue (eight moment identifications at the re-centred pair + the
  assembly, no known obstruction). Restoration = re-running that assembly on the retained
  machinery; the generic `cornishFisher_of_edgeworth` is proved, so the corollary is recoverable
  verbatim.

**Documented statement deviations (all in-file):** the eight-moment hypothesis the studentized
development used (vs the classical four) is recorded in the removal note's history; the
convex-sets Berry–Esseen carries the log-power and `C ≍ k` deviations.

**Axioms audit:** 8 surviving headliners (`berryEsseen_convex_sharp`, `edgeworth_mean_uniform`,
`cornishFisher_of_edgeworth`, `exists_fourierCertificate_deltaSurrogate`,
`exists_studentized_middle_range_gap_bound`, `smoothStat_largeK_weakConverges_gaussian`,
`ks_consistent`, `randTest_exact_level`) checked via a temporary `StatLean/AxiomsAudit.lean` —
expected `propext`/`Classical.choice`/`Quot.sound` only (result recorded in the merge commit).

**Verification-pattern lesson (binding for future campaigns):** every wave from 34 through 53
overturned at least one predecessor claim (ingredient lists, transfer lemmas, moment reductions,
budget items, envelope shapes). Worked plans must instruct lanes to *verify every inherited
claim on contact*; docstring status blocks are claims, not ground truth.
