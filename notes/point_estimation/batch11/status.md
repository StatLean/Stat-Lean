# PointEstimation Batch 11 — orchestration status

Last update: 2026-07-15 (campaign start; design frozen, stubs in progress).

Integration branch: `pe/batch11` (off main 31c61ed). Proof branches `pe/<topic>` base off it. Merge to local `main` after full close (never GitHub origin without user request).

## Design decisions (frozen)

- **Model carrier (Batch 12 contract)**: bare `P : Θ → Measure 𝓧` + `[∀ θ, IsProbabilityMeasure (P θ)]` (no measurability-in-θ — kernels bridge via coercion). Dominated models via `ParametricFamily.toMeasure M μ θ := μ.withDensity (ofReal ∘ M.density θ)` (reuses AsymptoticStatistics.ParametricFamily, ℝ-valued densities). `Identifiable := Function.Injective P`.
- **Risk**: `risk P L δ θ = ∫⁻ L θ (δ x) ∂(P θ)` in ℝ≥0∞ (junk-value discipline); `riskRand` for `κ : Kernel 𝓧 D`; bridge to Mathlib `Probability.Decision` risk shape.
- **Exponential family**: `structure ExpFamily 𝓧 V` (V real inner-product space) with `base` (h absorbed: ν = h·μ), `stat`, `stat_meas`; `natSet := {η | Integrable (exp ⟪η,stat ·⟫) base}`; `logPartition = log ∫ exp⟪η,T⟫ dν`; **members via `Measure.tilted`** (junk = 0 measure off natSet); general form (5.1) via `IsCanonicalRepr`; `StatAffineIndep`, `FullRank`. Thm 6.22 needs only nonempty-interior; Cor 6.16 takes the affine-span condition.
- **Sufficiency**: primary per-A classical def `IsSufficient` (θ-free measurable κA with the defining lintegral property); workhorse `HasSufficientKernel P T := ∃ Q Markov, ∀ θ, (P θ).map (fun x => (T x, x)) = ((P θ).map T) ⊗ₘ Q` (compProd graph form — gives fiber support a.e. + Bayesian bridge by `snd`); `IsFactorizedDensity` a.e. form. Thm 6.1 = kernel composition (easy under this def); Rao–Blackwell via plain Jensen on Q-fibers (`ConvexOn.map_integral_le`), NOT conditional Jensen.
- **Completeness**: family-first `IsCompleteFamily` / `IsBoundedlyCompleteFamily` (both, for Batch 12); `IsCompleteStat := IsCompleteFamily (fun θ => (P θ).map T)`; `IsAncillary`. Basu stated with BOUNDED completeness.
- **UMVU**: variance-based `IsUMVU` over Δ = {∀θ, MemLp δ 2}; Thm 1.11(a) separately as risk-minimality for every nonneg convex loss.
- **Fisher info (PE-local, junk-safe)**: `score = deriv (density · x) θ / density θ x` (div-by-0 = 0); `fisherInfo = ∫ score² · density dμ`; s-dim `scoreVec`/`infoMatrix : Matrix (Fin s) (Fin s) ℝ`; bridge lemma to AsymptoticStatistics `fisherInformation`. CR bound with explicit USER-INPUT regularity (5.29)/(5.30); Thm 5.15 discharges the δ-side conditions from density-side (5.38).
- **Equivariance**: general via `[Group G] [MulAction G 𝓧/Θ/D] [MeasurableSMul G 𝓧]`, induced Θ-action as data; `IsInvariantModel/IsInvariantLoss/IsEquivariant/IsRiskUnbiased`; transitivity = `MulAction.IsPretransitive`. Location §3.1 developed CONCRETELY on `Fin n → ℝ` (`P ξ = P₀.map (· + ξ•1)`, `diffs` statistic). Shared `ConditionalRiskEngine` (condDistrib over orbit statistic + pointwise a.e. minimizer ⇒ global optimality) instantiated by location/scale/location-scale. `pitmanEstimator` = closed-form ratio of integrals.
- **Linear models**: `canonicalNormal η σ² := Measure.pi (gaussianReal ∘ η)`; mean subspace `Submodule ℝ (EuclideanSpace ℝ (Fin n))`; LSE = `orthogonalProjection`; Gauss–Markov moments-only. Reuse PiGaussian, chiSquared (MultipleTesting), stdGaussian_eq_map_pi_orthonormalBasis.

## Named deferrals (pre-agreed)

- TSH 2.6.1 GENERAL standard-Borel per-A⇒kernel gluing (statement + documented deferral); the dominated+standard-Borel version — the one Batch 12 consumes — is fully proved.
- Thm 4.14(c) (book proof = "see Problems 4.16–4.18"): statement + deferral.
- Thm 5.12 (attainment ⇒ direction): extra USER-INPUT C¹-in-θ regularity, documented deviation.
- Conditional: s-dim Thm 5.8 full joint analyticity (fallback freeze: continuity + HasFDerivAt + all-order partials — covers all downstream uses); Cor 1.11 measurable-argmin brick (only Cor 1.11 renegotiates if it stalls).

## Work items (19) — 3 concurrent lanes, rolling waves

Deps: P = proofs merged; s = stubs only.

| # | id | wave | size | headliners | deps |
|---|---|---|---|---|---|
| 1 | pe/expfam-core | 1 | M | natSet convex, P η prob., densities, products, Thm 5.10, (5.14)/(5.15), Thm 5.17 | s |
| 2 | pe/mgf-uniqueness | 1 | L | 1-D Laplace uniqueness + signed corollary | — |
| 3 | pe/sufficiency-risk | 1 | M | kernel⇒per-A, fiber support, Thm 6.1, Bayesian bridge | s |
| 4 | pe/hs-bricks | 2 | L | Halmos–Savage mixture existence; condExp-withDensity | — |
| 5 | pe/completeness-expfam | 2 | L | s-dim mgf uniqueness (box); Thm 6.22 (1-D + s-dim) | 2P |
| 6 | pe/umvu-core | 2 | M | Lem 1.4, Thm 1.7, Thm 5.1(§2.5), Rao–Blackwell | s |
| 7 | pe/sufficiency-factorization | 3 | L | TSH 2.6.2; Cor 2.6.1 (both directions) | 4P |
| 8 | pe/basu-minimal | 3 | M | Thm 6.21 Basu; Thm 6.12; Cor 6.13; Cor 6.16 | 1P, 3s |
| 9 | pe/cramer-rao | 3 | M/L | Lem 5.3; Thm 5.10 CR; (5.32); Thm 5.15+Cor 5.17; Thm 5.8(§2.5)+Cor 5.9 | s |
| 10 | pe/lehmann-scheffe | 4 | M | Lem 1.10; Thm 1.11(a)(b); Cor 1.12 | 6P, 5P, 3P |
| 11 | pe/expfam-smoothness | 4 | L | Thm 5.8(§1.5) smoothness; Lem 5.15 Stein | 1P |
| 12 | pe/equivariance-general | 4 | M | argmin+convex bricks; Thm 2.7; Cors 2.8/2.13; Thm 2.17 | s |
| 13 | pe/location | 5 | L | Thm 1.4; Lems 1.6/1.7; Thm 1.8; engine; Thm 1.10; Cors 1.11/1.12/1.14; Thm 2.15; Lem 1.23/Thm 1.27 | 12P |
| 14 | pe/info-multiparam | 5 | L | Thm 5.4; Thm 6.2; Thm 6.1; Thm 6.6; Thm 5.12 | 1P, 9P |
| 15 | pe/linear-model-umvu | 5 | L | canonical completeness; Thm 4.3(a); Thm 4.4; Thms 4.8/4.10; Thm 4.12; Cor 4.13 | 5P, 10P |
| 16 | pe/pitman | 6 | L | Thm 1.20 Pitman = MRE | 13P |
| 17 | pe/scale | 6 | M/L | Thm 3.1; Thm 3.3; Cors 3.4/3.8; Thm 3.17 | 13P |
| 18 | pe/linear-model-mre | 7 | L | Thm 4.3(b)(c); Cor 4.5; Thm 1.17 + X̄-MRE; Thm 4.14(a)(b) | 8P, 13P, 15P, 17P |
| 19 | pe/sufficiency-regcond | 4–7 | XL | TSH 2.6.1 (dominated proved; general deferral-eligible) | 7P |

Layering: ForMathlib → Model → {ExponentialFamily, Sufficiency, Completeness} → {UMVU, InformationInequality} → {Equivariance, LinearModel}. Sufficiency/Completeness NEVER import UMVU/Equivariance (Batch 12 imports the former only).

## Ledger

See outline.md for the 73-item book↔Lean dictionary (Lean names filled as stubs land).

## Statement-first stub phase — COMPLETE (2026-07-18)

57 files, 176 sorry-stubs, drafted by a 6-agent fan-out, all committed on `pe/batch11`.

| Directory | Files | Stubs |
|---|---|---|
| ForMathlib | 8 | 23 |
| Model | 1 | 0 (defs only) |
| ExponentialFamily | 7 | 24 |
| Sufficiency | 8 | 19 |
| Completeness | 3 | 6 |
| UMVU | 5 | 11 |
| InformationInequality | 8 | 19 |
| Equivariance | 11 | 48 |
| LinearModel | 6 | 26 |

### Stub-gate results (cluster, `lean-fasrc-build --worktree pe/batch11`)

- ForMathlib (8 modules): **GREEN**, 2856 jobs, 0 errors, 23 sorries.
- Defs + Sufficiency + UMVU: **1 error** — `InformationInequality/Defs.lean:72` type mismatch on
  `scoreVec`. FIXED (laptop, `Defs.lean` is laptop-only): at pin v4.29.1 `WithLp` is a *structure*,
  not a type synonym, and there is no `Coe (∀ i, α i) (PiLp p α)`, so the bare lambda does not
  elaborate to `EuclideanSpace`. Must be built with `WithLp.toLp 2 (fun i => …)` — the idiom the
  rest of the repo already uses (`ParametricFamily/SubmodelDQM.lean:52`). Everything else green.
- ExponentialFamily + Completeness + InformationInequality (post-fix): **GREEN**, 2840 jobs, 0 errors.
- Equivariance + LinearModel: **GREEN** after two fixes (open scoped NNReal for the `ℝ≥0`
  notation; annotate the competitor binder `δ'` so `IsCanonicalMRE`'s implicit dimensions infer).
- **FULL-AREA GATE GREEN (2026-07-18): `lake build StatLean.PointEstimation` — 0 errors,
  175 sorries, `Build completed successfully`.** Area umbrella `StatLean/PointEstimation.lean`
  created (laptop-only surface); not yet imported by `StatLean.lean` (that happens at merge).

### Statement decisions & honest corrections made during drafting

Mathematical catches (statements would have been false or laundered as originally briefed):
- **Thm 5.10 needs `E.base ≠ 0`.** For the zero reference measure the identity reads `0 = 1`. The
  1-D moment identities (5.14)/(5.15) do NOT need it — both sides degenerate to 0, matching
  Mathlib's `integral_tilted_mul_self`/`variance_tilted_mul`.
- **Cramér–Rao needs `HasCommonSupport`.** Without it the theorem is FALSE: the junk-safe score
  vanishes off the support while `∫ δ ∂p` still sees that region. This restores a standing
  hypothesis of the source's §2.5 rather than adding one. Also `AEStronglyMeasurable (score …)` is
  unavoidable (the score is a `deriv`; the integrability of `score²·p` cannot recover its sign).
- **Thm 4.14(c) is false as printed** for an a.s. constant design (the fixed-design theorem then
  does supply a BLUE). Stated with an explicit nondegeneracy hypothesis, marked DEFERRAL-ELIGIBLE.
- **Thm 1.27 needs neither convexity nor evenness** — the source's proof only applies MRE
  minimality to the equivariant `δ − a`. Stated hypothesis-free.
- **Thm 2.15 does not use the invariant-model hypothesis** (only transitivity, loss invariance,
  commutativity, minimality); dropped as dead weight.
- **`unique_unbiased_function_of_complete` needs only completeness**, not sufficiency (strengthening).
- Fiber integrability in Rao–Blackwell/Lehmann–Scheffé is DERIVED from the reconstruction identity,
  never hypothesized (anti-laundering).

Scope/route decisions:
- Thm 5.8 (§1.5) full s-dim joint analyticity is a separate DEFERRAL-ELIGIBLE stub; the
  continuity + `HasFDerivAt` + all-order-partials forms cover every downstream consumer.
- Thm 1.17 is the source's short comparison argument (r_n maximized at the normal). The
  Kagan–Linnik–Rao uniqueness is quoted-not-proved in the source and is OUT of scope.
- Cor 3.8: both the Stein-loss form and the standardized squared-error form are stated (both are
  source content; the brief named the latter).
- Lem 6.14 omitted (not in the outline ledger); Lem 1.23(c) omitted (needs the UMVU layer, which
  the Equivariance layer may not import).
- Cor 5.17 is the source's "score has mean zero" (not the iid statement); the iid form ships under
  the requested name `cramer_rao_iid` as the source's (5.33).
- Equivariance uses `MeasurableConstSMul` (weaker than the design note's `MeasurableSMul`; nothing
  integrates over the group). LinearModel keeps equivariance as explicit functional equations on
  competitors rather than the general `MulAction` framework.
- `Matrix` has no `MeasurableSpace` instance at this pin → random designs use `Fin k → Fin l → ℝ`.

## Event log

- 2026-07-15: design frozen (19 items ≈7 waves, ~42 files); pe/batch11 cut off main 31c61ed, pushed to cannon; ledgers committed.
- 2026-07-18: weekly-quota interruption killed 13 of 14 draft agents; scratchpad worktrees lost (committed work intact). Worktrees recreated, cluster re-authed, full fan-out relaunched.
- 2026-07-18: stub phase COMPLETE — 57 files / 176 stubs committed; ForMathlib and ExpFamily/Completeness/InfoIneq gates green; scoreVec contract bug found by gate + agent and fixed.

## Proof-closure phase (started 2026-07-18)

Rolling 3-lane cluster fan-out (`lean-fasrc-fan-out`, detached tmux + srun). Per-item prompts
under `.claude/prompts/pe-*.md`. Each item: closed on its own `pe/<topic>` branch → harvested →
touch-set audit → merged `--no-ff` into `pe/batch11` → integration gate.

### Wave 1 — COMPLETE, all three items 0-sorry and axiom-clean

| item | files | sorries closed | axioms | notes |
|---|---|---|---|---|
| `pe/mgf-uniqueness` | ForMathlib/MGFUniqueness | 4 → 0 | clean | Laplace-transform uniqueness. Route: tilt at an interior point so `0 ∈ interior (integrableExpSet)`, local `Set.EqOn` mgf identity theorem seeded via `interior_maximal` (Mathlib's needs *global* equality), strip preconnectedness from `Convex.inter`/`.linear_preimage Complex.reLm`, restrict to the imaginary axis (`complexMGF_id_mul_I`) → `Measure.ext_of_charFun`, untilt with `withDensity_inv_same`. |
| `pe/sufficiency-risk` | Sufficiency/{Basic,RiskEquality,BayesianBridge} | 9 → 0 | clean | Thm 6.1 came out as pure kernel-composition associativity, exactly as the graph/`⊗ₘ` design predicted — no conditional expectation anywhere. `hasSufficientKernel_fiber` needed `upgradeStandardBorel` for `MeasurableEq S`. |
| `pe/expfam-core` | ExponentialFamily/{Basic,MGF,NaturalStatistic} | 17 → 0 | clean | `natSet_convex` via weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`) + `Integrable.mono'`. The `E.base ≠ 0` nondegeneracy hypotheses were **used, not circumvented**. Imports `AsymptoticStatistics.ForMathlib.PiWithDensity` — sanctioned (ForMathlib layer, DAG-forward). |

**No false statements found; no escape-hatch sorries used.** PE sorry count 175 → 146.
Integration gate after the first merge: 0 errors, `Build completed successfully`.

### Process findings

- **`CLAUDE.md` is gitignored, so it does not exist in cluster worktrees.** Prompts that said
  "read the repo `CLAUDE.md` first" were pointing at a missing file. All prompts now inline the
  rules they need. (Same applies to `notes/`, `tools/`, `.claude/` — use `git add -f`.)
- Do **not** pre-create a cluster worktree with `lean-fasrc-worktree-add` for a branch you intend
  to hand to `lean-fasrc-fan-out`: the wrapper creates its own and dies with
  "already used by worktree". Let fan-out own the lifecycle.
- Proof branches cut before an earlier merge land as normal merges; verify the earlier closure
  survived (`grep -c sorry`) rather than assuming.

### Waves 2–5 — merged results (PE sorry count 175 → 74, 58% closed)

| item | outcome | notes |
|---|---|---|
| `pe/completeness-expfam` | **0 sorry, axiom-clean** | Thm 6.22 + s-dim Laplace uniqueness. Multivariate case done by a **Cramér–Wold reduction reusing the closed 1-D brick as a black box** — the compositional payoff of the ForMathlib layering. |
| `pe/umvu-core` | **0 sorry, axiom-clean** | `isUMVU_unique` via the **parallelogram identity** (Mathlib has no packaged covariance Cauchy–Schwarz). Rao–Blackwell exactly as designed: plain per-fiber Jensen; **fiber integrability derived** via `Measure.integrable_compProd_iff`, no added hypotheses. |
| `pe/hs-bricks` | **0 sorry, axiom-clean** | Halmos–Savage by maximizing `ν₀(⋃ supp)` over countable subfamilies (`exists_seq_tendsto_sSup`, sequences merged with `Nat.unpair`), maximality forcing domination. |
| `pe/equivariance-general` | 4/5 files 0-sorry | Thm 2.7 + argmin/convex/IBP bricks closed. **Thm 2.17's analytic core lifted to a named `private` debt** with a precise TODO (exponent-progression argument); the two public theorems are closed on top of it. |
| `pe/cramer-rao` | 3/4 files 0-sorry | **Cramér–Rao itself closed**, plus score basics and Fisher additivity. One named debt: `diff_under_integral_core`, the dominated-convergence step of family-side differentiation under the integral — every downstream theorem is a genuine reduction to it. |
| `pe/sufficiency-factorization` | 3/4 files 0-sorry | Halmos–Savage criterion, **Fisher–Neyman factorization (both directions)**, minimal sufficiency via the likelihood-ratio vector — all axiom-clean. Remaining sorry is exactly the **pre-agreed TSH 2.6.1 general deferral**; its comment records that no result in the area consumes it (all users route through the dominated version, which is closed). |
| `pe/location` | 3/4 files 0-sorry | Location structure (Thms 1.4/1.8, Lems 1.6/1.7), the shared **conditional-risk engine**, Thm 1.10, Cor 1.12, and all risk-unbiasedness closed. Cor 1.11 (convex existence) and Cor 1.14 (bounded loss) cores remain named debts — exactly the renegotiation point the design predicted. |

| `pe/basu-lehmann` | 1/3 files 0-sorry | **Basu (Thm 6.21) closed axiom-clean.** Lehmann–Scheffé uniqueness (Lem 1.10) and the convex-risk form (Thm 1.11b) closed. Two **contract-level** gaps surfaced — see below. |

**No false statements found in any item to date.** Every debt is a named, documented `private`
lemma with a TODO, never a weakened public statement.

## OPEN DESIGN QUESTION — two gaps in contracts I froze (needs a scope decision)

These are not proof difficulties. They are places where the frozen `Defs` are too weak (or the
ambient structure too poor) for the intended route, found and documented by the proof session
rather than worked around.

**(1) `IsUMVU`'s competitor class is not measurable enough for kernel Rao–Blackwell.**
The frozen `IsUMVU` quantifies minimality over competitors carrying only `MemEstL2 P δ'`, i.e. a
*per-parameter* `AEStronglyMeasurable` representative. The kernel route needs one **global
measurable** representative (the kernel average `t ↦ ∫ δ' dQ_t` and the completeness test
function must be genuinely measurable with identically zero mean). Per-parameter representatives
do **not** glue into a global one — the session gives **Dirac families as a counterexample** —
and the signature supplies no dominating measure.
Options: **(a)** add `Measurable δ'` to the competitor condition in `IsUMVU`/`IsLMVU` (faithful to
the classical convention that an *estimator* is a measurable function, but formally a weakening,
and it forces a re-gate of everything that consumes `IsUMVU`); **(b)** build a `condExp`-based
Rao–Blackwell layer, which needs only integrability and avoids the kernel entirely; **(c)** keep
the strong statement and carry the gap as a standing named debt.
Currently **(c)** — statement intact, `variance_rbEstimator_le_of_complete` left as a documented
`private` debt. Recommend **(b)** as the principled fix; it is additive (new layer, no re-gate).

**(2) Cor 1.12 (`isUMVU_of_fullRank_expFamily`) lacks the structure to build its sufficiency
kernel.** It consumes `HasSufficientKernel P E.stat`; for a general reference measure that kernel
comes from `hasSufficientKernel_of_isSufficient`, which needs `[StandardBorelSpace 𝓧]` (and
`[Nonempty 𝓧]`) — neither is in the frozen signature, and an exponential family supplies no
explicit reconstruction kernel without such structure. Completeness itself transfers cleanly; the
sufficiency kernel is the only missing input.
Fix: add the two instance binders to that corollary's signature (standard throughout this
literature — every sufficiency theorem in the area already carries them). Cheap and local.

### Waves 6–8 — merged results (PE sorry count now **46**, from 175: **74% closed**)

| item | outcome | notes |
|---|---|---|
| `pe/expfam-info` | 2/5 files 0-sorry | **Multiparameter Cramér–Rao (Thms 6.1/6.6) closed** (matrix Cauchy–Schwarz), **Stein identity closed**, 1-D analyticity closed, `cramer_rao_attained_of_affine` (⇐) closed. Multivariate smoothness (4 gaps) and the Attainment ⇒ direction remain — both were pre-identified fallback candidates. |
| `pe/scale-pitman` | partial | Scale structure (6/7), Stein-loss + standardized-squared scale MRE, Pitman measurability/equivariance, **Thm 1.17 (normal least favourable) closed**. **TWO FALSE STATEMENTS FOUND — see below.** Pitman/LocationExamples debts were blocked by an unscheduled dependency (my error, now scheduled). |
| `pe/linear-model` | 1/5 files 0-sorry | **Gauss–Markov + BLUE closed (Thm 4.12/Cor 4.13)** — pure projection geometry, as designed. Canonical-model completeness transport and the orthonormal-basis reduction did not land in one session; 15 gaps remain across the other four files. |

## FALSE STATEMENTS FOUND (with counterexamples) — statements need fixing

Both were found by proof sessions instructed to stop and report rather than weaken. Neither
has been "fixed" by weakening; both are recorded as sorried with the counterexample in-file.

1. **`isScaleMRE_of_conditional_min` is FALSE as stated.** The conditional-minimality
   hypothesis `hmin` quantifies only over **positive** `w`, but `IsScaleEquivariant` admits
   competitors of either sign, so `hmin` cannot dominate an opposite-sign competitor.
   Verified counterexample in the session report. Fix options: quantify `hmin` over all
   `w ≠ 0`, or restrict the competitor class to positive-valued estimators (the classical
   reading, since the estimand `τʳ > 0`). `exists_isScaleMRE_of_convex` is blocked by it.
2. **The `mpr` direction of the measurable scale factorization is FALSE.** A non-Borel subset
   of the null hyperplane `{xₙ = 0}` breaks it. The set-level version and the `mp` direction
   are fine and closed.

## Scheduling error (mine, corrected)

`ForMathlib/CondDistribDensity.lean` was never assigned to a work item, so its 3 stubs
blocked `Pitman.pitmanEstimator_eq_sub_condMean` and `LocationExamples.isLocMRE_mean_gaussian`
— those debts are *dependency* artifacts, not mathematical obstacles. Item
`pe/conddensity-pitman` now closes the brick and the two downstream results.

### In flight

`pe/conddensity-pitman` (the unblock above), `ht/test-foundations` (Batch 12's first item:
NP lemma, quantiles, p-values, confidence duality), `ht/invariance-core` (Batch 12).

## Corrections the proof sessions made to MY briefs (2026-07-19)

Recording these because they were errors in the orchestration, not in the mathematics, and
the same mistakes would otherwise recur in Batch 12.

1. **Wrong natural statistic for the canonical normal model.** My brief prescribed
   `T y = (y₀,…,y_{s−1}, Σ_{j≥s} yⱼ²)` (residual SS). That is **not** a canonical exponential
   family: the Gaussian log-density retains `−(1/2σ²)·Σ_{i<s} yᵢ²`, which depends on both the
   data and `σ²`, so it is neither part of `⟨η,T⟩` nor absorbable into a θ-free carrier.
   Correct route: use the **total** sum of squares `Σ_all k yₖ²` with `base = volume`, `h = 1`,
   then transport completeness along the measurable bijection
   `(a, total) ↔ (a, total − Σ aᵢ²) = (head, RSS)`.

2. **Sorry-taint propagation through Lehmann–Scheffé.** `isUMVU_of_complete_sufficient` calls
   the private `variance_rbEstimator_le_of_complete`, which is the OPEN `IsUMVU`
   measurability debt. Anything routed through it therefore reports `sorryAx`, even though the
   file itself looks closed. **This is exactly the trap the charter warns about: a clean-looking
   compile can still be axiom-tainted.** The axiom-clean alternative is
   `isUMVU_iff_uncorrelated_unbiasedZero` (fully proven). For the normal linear model the
   measurability gap is *locally* closable, because all `canonicalModel` members are mutually
   absolutely continuous (strictly positive Gaussian densities), so a `P p₀`-a.e. representative
   is automatically a `P p'`-a.e. representative for every `p'`.

   **Implication for the endgame audit:** the `#print axioms` sweep must cover every public
   headline, not a sample — the taint is invisible to `grep -c sorry` on the consuming file.

3. **Realistic sizing.** `gaussianVector` had *zero* existing helper lemmas; the whole
   moment / density / mutual-a.c. / exp-family-recognition / orthonormal-transport theory has to
   be built from scratch (~250–350 lines for the completeness hinge alone). The LinearModel group
   is multi-session work and has been re-scoped to a single-hinge item
   (`pe/canonical-completeness`) with commit-after-every-lemma discipline.

## Proof-closure scoreboard (2026-07-19) — PE sorry count **175 → 29 (83% closed)**

Closed and merged, axiom-clean unless noted. Every item was independently harvested, audited
against its touch-set, and merged `--no-ff` into `pe/batch11`.

**Fully closed files:** all of `ForMathlib` (8), `Model`, `ExponentialFamily/{Basic,MGF,
NaturalStatistic}`, `Sufficiency/{Basic,RiskEquality,BayesianBridge,HalmosSavageCriterion,
Factorization,Minimal}`, `Completeness/{Basu,ExpFamily}`, `UMVU/{Basic,CovarianceCriterion,
RaoBlackwell}`, `InformationInequality/{Basic,CramerRao,Additivity,Multiparameter}`,
`Equivariance/{General,LocationStructure,ConditionalRiskEngine,RiskUnbiased,Pitman}`,
`LinearModel/{Canonical,GaussMarkov}`.

**Headline theorems proven:** Laplace-transform uniqueness (1-D and s-dim, the latter by a
Cramér–Wold reduction reusing the 1-D brick); exponential-family completeness (Thm 6.22);
Fisher–Neyman factorization both directions; Halmos–Savage; minimal sufficiency; Basu
(Thm 6.21); Rao–Blackwell; the covariance criterion (Thm 1.7); Cramér–Rao (Thm 5.10) and its
multiparameter matrix form (Thms 6.1/6.6); Stein's identity; sufficiency risk-equality
(Thm 6.1, which came out as pure kernel-composition associativity exactly as the graph/⊗ₘ
design predicted); the location MRE theory including the shared conditional-risk engine
(Thm 1.10, Cors 1.12); **Pitman (Thm 1.20)**; Thm 1.17; Gauss–Markov and BLUE (Thm 4.12,
Cor 4.13); the canonical normal model end to end — complete sufficiency plus the UMVU trio
(Thm 4.3a); random-design regression UMVU and covariance (Thm 4.14a,b).

## Statement defects found and FIXED (each caught by a session that refused to prove it)

1. **`scoreVec` did not elaborate** — at this pin `WithLp` is a structure, not a type synonym;
   fixed with `WithLp.toLp 2`. (Also caught independently by the stub gate.)
2. **`isScaleMRE_of_conditional_min` was FALSE** — `hmin` ranged only over positive `w` while
   the equivariant class is `δ₀/w` over the *nonzero* reals, so opposite-signed competitors
   were never dominated. Explicit counterexample (r = 0, δ₀ ≡ 1, wStar ≡ 1, γ rewarding
   negatives). **Fixed:** quantify over all `w ≠ 0`, matching the location case.
3. **`pitmanEstimator_eq_sub_condMean` was unprovable as stated** — a pointwise (`∀ x`) claim
   about a `condDistrib`, which is only determined a.e. **Fixed:** relaxed to `∀ᵐ x`; the whole
   Pitman development then closed 0-sorry.
4. **Cor 1.12 lacked the structure to build its sufficiency kernel** — added
   `[StandardBorelSpace 𝓧] [Nonempty 𝓧]`, standard throughout this literature.
5. **Thm 4.14(c) is false as printed** for an a.s. constant design; carries an explicit
   nondegeneracy hypothesis and remains a sanctioned deferral.

## Orchestration errors of mine, corrected

- Prescribed the **residual** sum of squares as the canonical model's natural statistic; that
  leaves a `−(1/2σ²)Σ_{i<s} yᵢ²` term depending on both data and parameter, so it is not an
  exponential family. Correct route: **total** SS plus a shear transport. The session caught it.
- **Sorry-taint propagation:** `isUMVU_of_complete_sufficient` compiles and its file greps clean,
  yet it calls the private lemma holding the `IsUMVU` measurability debt — so anything proven
  through Lehmann–Scheffé reports `sorryAx`. The endgame audit must `#print axioms` **every**
  public headline, not a sample.
- `ForMathlib/CondDistribDensity` was never assigned to a work item; two downstream results were
  blocked by a missing dependency rather than by mathematics.

## Remaining 29, by kind

- **Awaiting a scope decision (2):** the `IsUMVU` competitor-measurability gap in
  `LehmannScheffe`. Options recorded above; recommendation remains a `condExp`-based
  Rao–Blackwell layer (purely additive, no re-gate).
- **Genuine analytic work (≈17):** multivariate smoothness (4), the Gaussian isometry transport
  in `LeastSquares` (3), the canonical/subspace MRE clauses in `Equivariant` (4), scale MRE (4,
  now unblocked by fix #2), `LocationMRE`'s two regularity cores.
- **Sanctioned deferrals (5):** TSH 2.6.1 general gluing, Thm 4.14(c), Thm 5.12 (⇒),
  Thm 5.8 s-dim joint analyticity, Thm 2.17's analytic core — each a named `private` lemma with
  a precise TODO, none consumed by any other result.

### VERIFIED integration gate (2026-07-19)

`lake build StatLean.PointEstimation` on the cluster: **0 errors, `Build completed successfully`,
26 sorried declarations** (down from 175 at the stub gate — **85% closed**). The build warning
count is the authoritative inventory; a `grep -c sorry` over the tree reports 29 because it also
matches docstring and TODO mentions.

## Two structural findings on the remaining tail (2026-07-19)

### 1. `ForMathlib/MeasurableArgmin.exists_measurable_argmin` is INAPPLICABLE as stated — my design error

The brick requires **continuity** of the `ℝ≥0∞`-valued objective in the scan variable. I chose
continuity over lower semicontinuity deliberately at stub time, reasoning that it "keeps the
selection elementarily provable" and noting the LSC strengthening in the header.

That choice makes the brick **unusable by its two intended consumers**
(`LocationMRE.exists_measurable_condMinimizer_convex` and
`ScaleMRE.exists_isScaleMRE_of_convex`): their objective `w ↦ ∫⁻ ofReal(ρ(δ₀· − w)) ∂κ(z)` is
convex but can **jump finite → ∞** at the boundary of its finiteness domain — constructible with
an asymmetric-growth convex `ρ` and a heavy-tailed conditional kernel. So `Continuous` genuinely
fails in general and the two convex-MRE existence theorems cannot route through it.

Options: **(a)** restate the brick with lower semicontinuity (the honest form; needs real
measurable-selection machinery — Kuratowski–Ryll-Nardzewski); **(b)** add a finiteness/growth
hypothesis to the two consumers restricting to losses whose conditional risk is finite on a
neighbourhood; **(c)** leave both consumers as named debts. Currently **(c)**. Recommend **(b)**
as the cheap sound fix and **(a)** as the right one — this is a scope call.

### 2. `ScaleStructure`'s measurable-factorization `mpr` is CONFIRMED genuinely FALSE

Not a missing hypothesis: a global `Measurable u` cannot be recovered from a factorization that
holds only off a null set, because `{xₙ = 0}` is Borel-isomorphic to `ℝᵐ` and therefore carries
non-Borel subsets. The set-level version and the `mp` direction are true and closed. A sound
restatement would conclude a.e.-measurability, or assume a complete σ-algebra. Left as a
documented obstruction with the counterexample in-file.
