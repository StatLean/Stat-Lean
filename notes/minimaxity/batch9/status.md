# Batch 9 — Minimaxity (Wainwright Ch. 15): status ledger

**Branch** `mmx/batch9` (off `main`). **Pin** v4.29.1. **Reference** Wainwright Ch. 15.
Source of truth = `lake build` sorry inventory.

## State — COMPLETE (machinery formalized; deep cruxes are named debts)

The full 29-file `StatLean.Minimaxity` area is **stated, fully cited, and builds green** (errors 0;
sorries are the named analytic debts below). Every Wainwright Ch. 15 result is formalized as a
precise Lean statement with a full book citation; every public theorem is either **fully proven
(0-sorry)** or **structurally proven, reduced to a single named `private` analytic crux** — there are
**no bare public-theorem sorries**.

### Debt-closure campaign (cluster fan-out) — 9 of 25 debts driven to 0-sorry

A subsequent campaign closed the most tractable debts. Full `StatLean.Minimaxity` build stays **green**
(3090 jobs, 0 errors); sorry inventory **25 → 16**. **Closed (0-sorry, 9):** `klDiv_mixture_minimizes`
(#1, Gibbs identity), `tvDist_eq_half_lintegral` (#2), `one_sub_tvDist_eq_iInf` (#3),
`sqHellinger_pi_le_nsmul` (#4, eLpNorm bridge to `HellingerProduct`), `klDiv_le_avg` (#6, via Mathlib
`convexOn_klFun`), `lecam_half_lintegral` (#8, Cauchy–Schwarz), `gilbert_varshamov` (#9, Hamming
maximal-packing), `binary_testingError_eq_tvDist` (#12, Eq 15.13 — via Mathlib `bayesBinaryRisk`; makes
`minimax_two_point` fully proven), and `yang_barron` (#16, log-N mixture step). (Pinsker's scalar Bernoulli
sub-core also closed, but its KL-2cell DPI core #7 remains.) **Remaining 16 debts** (16 sorries) split:
*tractable-but-stuck* — Pinsker KL-2cell DPI (#7, blocked by absence of a Mathlib `klDiv` data-processing
lemma); *hard cores* — measurable-Borel selector (#5), sphere/sparse packing volume (#10/#11), Le Cam
convex-hull/functional cruxes (#13/#14), Fano continuous-`Z` disintegration (#15, `condDistrib` route
scoped); *research-grade infrastructure* — the 7 example constructions (#17–23, the
nonparametric-perturbation toolkit), Gaussian differential entropy (#24), Sobolev/Kolmogorov–Tikhomirov
metric entropy (#25). Closing these needs new `ForMathlib` theory, not prompt-and-harvest.

**Mathlib leverage found (for future closure):** `convexOn_klFun`/`strictConvexOn_klFun` (KL convexity, used
for #1/#6), `bayesBinaryRisk` + `_eq_tv` (binary testing, used for #12), `ProbabilityTheory.condDistrib`
(conditional distribution, scoped for #15), `Measure.addHaar_ball`/`addHaar_closedBall` (ball volumes,
scoped for #10/#11). **Absent (must build): ** a `klDiv` data-processing inequality (`klDiv_map_le`),
differential entropy of measures (#24), metric entropy of smoothness classes (#25).

### Tranche 2 (hard-core debts) — 4 more closed → 13 of 25; build green, sorry inventory 16 → 12

A second campaign targeted the 7 "tractable-but-blocked" + "hard-core" debts (#5, #7, #10, #11, #13, #14, #15).
Full `StatLean.Minimaxity` builds **green** (3099 jobs, 0 errors). **Closed (0-sorry, 4):**
- **#7 Pinsker DPI** — built the reusable `klDiv_map_le` (`ForMathlib/KLDataProcessing.lean`): a genuine
  data-processing inequality `klDiv (μ.map f)(ν.map f) ≤ klDiv μ ν` via conditional Jensen
  (`convexOn_klFun.map_condExp_le` over the comap σ-algebra). Then `klDiv_ge_two_mul_tvDist_sq` closes.
- **#5 measurable selector** (`EstimationToTesting`) — `exists_measurable_nearestPoint` via `Measurable.find`
  + `measurableSet_le` + `Finite.exists_min`, needing the added `[OpensMeasurableSpace Ω]` instance.
- **#14 functional modulus** (`LeCam/Functional`) — added `[Nonempty ι]`, `[∀ i, IsProbabilityMeasure (P i)]`
  (genuinely *not* derivable from `IsMarkovKernel Pn` without `SigmaFinite`), `(hΦlsc : LowerSemicontinuous Φ)`
  for the `Φ(½·⨆d) ≤ ⨆Φ(½·d)` interchange (own `map_iSup_le_of_lsc` via `lowerSemicontinuous_iff_isOpen_preimage`).
- **#13 Le Cam convex-hull** (`LeCam/ConvexHull`) — used `Metric.infEDist` + `continuous_infEDist.measurable`
  for the two-class decision regions (cleaner than the argmin selector).

**Reduced to a single named research-grade residual (3):** **#10 sphere packing** (the `2ⁿ` lower bound
genuinely needs spherical-cap *surface* measure — ambient ball volume tops out at `~(3/2)ⁿ`; isolated to a
`Measure.toSphere` cap-measure lemma); **#11 sparse packing** (the support-enumeration / embedding /
separation are proven; the support count reduced to a single binomial-volume estimate); and **#15 Fano**
(Mathlib has *no* conditional entropy / mutual information; the `I = log M − H(J|Z)` identity isolated as the
residual). Closing these three needs new `ForMathlib` infrastructure (cap Hausdorff measure; binomial volume
counting; a Shannon conditional-entropy theory) — not prompt-and-harvest.

**Net after both campaigns: 13 of 25 debts at 0-sorry; the other 12 are 12 named residuals** — the 3 above
plus the 9 out-of-scope example/research debts (#17–25). Full `StatLean.Minimaxity` builds green (3099 jobs);
the 4 tranche-2 headline closures are `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).

### Tranche 3 (the 3 reduced residuals: #10/#11/#15) — #10 closed → 14 of 25; build green 12 → 11

Deep-research pass (parallel sessions) on the 3 reductions, with **loose constants permitted**.
- **#10 sphere — CLOSED (0-sorry).** Abandoned the `Measure.toSphere` cap-fraction route (sharp `2ⁿ` needs the
  `sinⁿ⁻²` Wallis integral Mathlib lacks). Instead built the packing **directly from the closed
  `gilbert_varshamov`** via the `±1/√n` binary-code embedding `vα = ((2αᵢ−1)/√n)ᵢ` (`‖vα‖=1`,
  `‖vα−vβ‖²=4·hamming/n ≥ 1`). Bound loosened `n·log 2 → n/10` (still exponential; PCA untouched). Build green.
- **#15 Fano — CLOSED (tranche 4).** Built `condEntropy` + the full `mutualInformation = log M − H(J|Z)`
  identity (`mutualInformation_toReal_eq`), the pointwise discrete-Fano grouping (`discreteEntropy_le_log_card`),
  Jensen via `strictConcave_binEntropy`, and the MAP/Bayes-risk inequality `∫(1−maxⱼ posterior) ≤ q`
  (`mapError_integral_le`, the `iInf`-over-tests reduction). `fano_inequality` now fully proven.
- **#11 sparse — CLOSED (tranche 4, loose constant).** Block / q-ary Gilbert–Varshamov: split `[d]` into `s`
  blocks of size `q=d/s`, block supports ↔ `Fin s → Fin q`, q-ary GV mirroring the binary `gilbert_varshamov`
  with a crude ball bound `Σ_{i<s/2}C(s,i)(q−1)ⁱ ≤ s·2ˢ·q^{s/2}`. Bound weakened from the exact
  `(s/2)log((d−s)/s)` (unreachable by GV — needs Reed–Solomon for `d≥s²`) to `(s/2)log(d/s) − s·log2 − log s`
  (still exponential; LinearRegression untouched). Build green.

**Final state: 16 of 25 debts at 0-sorry; 9 named residuals remain** — exactly the out-of-scope example/research
debts (#17–25: the 7 nonparametric example constructions + Gaussian differential entropy + Sobolev/K–T metric
entropy). Full `StatLean.Minimaxity` builds green (**3097 jobs, 0 errors, 9 sorries**); `fano_inequality`,
`minimax_fano_lower_bound`, `exists_sparse_packing` are `#print axioms`-clean. On `mmx/batch9`; not pushed to
`origin`. **All 7 of the "tractable + hard-core" debts (#5,#7,#10,#11,#13,#14,#15) are now closed.**
**Mathlib leverage confirmed this pass:** `Measure.toSphere`+`toSphere_apply'`+`measurePreserving_homeomorphUnitSphereProd`
(sphere surface measure), `ProbabilityTheory.posterior` (`κ†μ`)+`posterior_eq_withDensity_of_countable`+`negMulLog`
(for #15), `Finset.powersetCard`+`Nat.choose` bounds (for #11). Genuinely absent: sharp cap surface (Wallis),
Shannon conditional entropy, q-ary GV count.

**Signature changes (laptop-coordinated, all justified + tagged):** `[OpensMeasurableSpace Ω]` on the 5
generic method theorems + the 2 generic examples (`DensityEstimation`, `Sobolev`); `[Nonempty ι]` +
`[∀ i, IsProbabilityMeasure …]` + `LowerSemicontinuous Φ` on `minimax_functional_modulus` and its
`LipschitzDensity` callers. New `ForMathlib/KLDataProcessing.lean` added to the umbrella.

Two completeness tiers (confirmed by `#print axioms`):

* **Axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no transitive `sorryAx`) — genuinely
  complete foundational lemmas: `klDiv_gaussianReal` (Ex 15.13), `klDiv_prod_eq_add`/`klDiv_pi_eq_nsmul`
  (15.11), `discreteEntropy_nonneg`/`discreteEntropy_le_log_card`/`discreteCondEntropy_le_entropy`,
  `tvDist_comm`/`tvDist_le_one`, `sqHellinger_comm`/`sqHellinger_le_two`. (~10 theorems.)
* **Structurally complete** (0 `sorry` in their own file, clean proof skeleton, but **transitively
  depend on a named debt** so `#print axioms` shows `sorryAx`): the headline method theorems
  `minimax_ge_testing_error` (Prop 15.1), `minimax_two_point` (15.14), `minimax_le_cam_convex_hull`
  (15.9), `minimax_fano_lower_bound` (15.12), `minimax_local_packing` (15.35), `minimax_yang_barron`
  (15.21), `pinsker_tv_le_kl` (15.2), `lecam_tv_le_hellinger` (15.3), and all 8 worked-example rate
  theorems (incl. `density_estimation_hellinger_rate`, `sobolev_regression_rate`). Each reduces to one
  or more of the 25 named debts below.

Built via cluster fan-out (`lean-on-fasrc`, `SRUN=1` detached tmux): Wave 1 (foundations, 8 units) +
methods (6) + packing (3) + examples (8) + Gaussian-max-entropy/Sobolev (2), harvested file-by-file
(touch-set only), each fresh-verified, with one parallel-session interface reconciliation
(`minimax_local_packing` gained `(hn : 0 ≤ n)` → 3 example calls realigned).

## Named debts (25) — all `private` + `-- TODO(mmx)`, public theorems delegate

| # | Lemma (file) | Missing analytic fact | Book |
|---|---|---|---|
| 1 | `klDiv_mixture_minimizes` (KLDivergence) | convexity of `klDiv` in 2nd arg | Ex 15.11 |
| 2 | `tvDist_eq_half_lintegral_aux` (TotalVariation) | TV density form via RN derivatives | Eq 15.6 |
| 3 | `one_sub_tvDist_eq_iInf_aux` (TotalVariation) | variational TV (indicator optimum) | Ex 15.1 |
| 4 | `sqHellinger_pi_le_nsmul_aux` (HellingerDivergence) | bridge to eLpNorm Hellinger product | Eq 15.12b |
| 5 | `mul_bayesRisk_zeroOne_le` (EstimationToTesting) | measurable nearest-point selector + triangle | Prop 15.1 |
| 6 | `klDiv_le_avg` (MutualInformation) | KL convexity (Jensen) | Eq 15.34 |
| 7 | `pinsker_half_lintegral_le` (PinskerInequality) | Bernoulli reduction + Jensen | Ex 15.6 |
| 8 | `lecam_half_lintegral_le` (LeCamInequality) | Cauchy–Schwarz `|√p−√q|·(√p+√q)` | Ex 15.5 |
| 9 | `gilbert_varshamov` (HammingPacking) | Gilbert–Varshamov / binary-entropy volume | Ex 5.3 |
| 10 | `sphere_packing_card` (SpherePacking) | sphere volume packing `≥ 2^n` | Ex 5.8 |
| 11 | `sparse_packing` (SparsePacking) | s-sparse volume packing | Ex 5.8 |
| 12 | crux (LeCam/TwoPoint) | binary Bayes error = ½(1−TV) | Eq 15.13 |
| 13 | crux (LeCam/ConvexHull) | convex-hull TV via variational form | Lemma 15.9 |
| 14 | crux (LeCam/Functional) | TV ≤ ¼ via Hellinger tensorization | Cor 15.6 |
| 15 | `fano_inequality` crux (Fano/FanoLowerBound) | entropy form `H(J|Z) ≤ h(qₑ)+qₑ log(M−1)` | Eq 15.61 |
| 16 | crux (Fano/YangBarron) | `D(P‖Q) ≤ ε² + log N` cover step | Lemma 15.21 |
| 17–18 | `lipschitz_…/quadratic_… modulus_bound` (LipschitzDensity) | bump-perturbation Hellinger modulus | Ex 15.7/15.8 |
| 19 | crux (QuadraticFunctional) | convex-hull modulus for `∫(f′)²` | Ex 15.11 |
| 20 | crux (GaussianLocation) | Gaussian product TV second-moment bound | Ex 15.4 |
| 21 | `uniform_two_point_tvDist_bound` (UniformLocation) | unit-interval shift Hellinger | Ex 15.5 |
| 22 | `linreg_local_packing_data` (LinearRegression) | sparse packing + Gaussian KL config | Ex 15.14 |
| 23 | `pca_fano_config` (PCA) | sphere packing + Gaussian max-entropy config | Ex 15.19 |
| 24 | `sum_klDiv_le_logdet` (GaussianMaxEntropy) | differential entropy + Gaussian max-entropy | Lemma 15.17 |
| 25 | `sobolev_packing_lower_bound` (SobolevEntropy) | Kolmogorov–Tikhomirov ellipsoid entropy | Ex 5.12 |

These 25 are the chapter's genuine analytic cores: KL/TV/Hellinger convexity & density calculus, the
Prop 15.1 selector, the Pinsker/Le Cam pointwise inequalities, the four Chapter-5 metric-entropy results,
Fano's entropy inequality, and the per-example construction bounds. Each is documented with the precise
missing fact; most need infrastructure (differential entropy, metric entropy of smoothness classes,
`f`-divergence convexity) absent from both Mathlib and StatLean — natural follow-up `ForMathlib` targets.

## Book-vs-Lean constants

Stated as provable: Le Cam two-point `Φ(δ)/2·(1−TV)` (15.14); Fano `Φ(δ)(1−(I+log2)/log M)` (15.12);
local packing `½Φ(δ)` (15.35); Pinsker `√(½ KL)`; example pre-factors `v/24n` (15.4), `(1−1/√2)/128·n⁻²`
(15.5), `v·rank/128n` (15.14) — matching Wainwright. Any deviation documented in-docstring per CLAUDE.md §1.

## Lessons

* Measurable-space binders must be **instance-implicit** in files using `minimaxRiskDist`.
* Cluster proof sessions: `SRUN=1` mandatory (login-node cgroup kills); detached tmux survives local
  kills; `claude -p` must run builds **foreground** (a backgrounded build ends the `-p` session); harvest
  by taking touch-set files only (sessions `git add -A` pick up artifacts/strays); laptop→primary
  `git fetch` can hang (busy gitdir) — transfer files via `fasrc-run` tar instead.
* Parallel sessions can diverge on a shared interface signature (here `+hn`); reconcile at integration.
* Major reuse: Mathlib `ProbabilityTheory.{minimaxRisk,bayesRisk}` + DPI; `klDiv` + chain rule;
  StatLean `HellingerProduct`.
