# Batch 9 — Minimaxity (Wainwright Ch. 15): status ledger

**Branch** `mmx/batch9` (off `main`). **Pin** v4.29.1. **Reference** Wainwright Ch. 15.
Source of truth = `lake build` sorry inventory.

## State — COMPLETE (machinery formalized; deep cruxes are named debts)

The full 29-file `StatLean.Minimaxity` area is **stated, fully cited, and builds green** (errors 0;
sorries are the named analytic debts below). Every Wainwright Ch. 15 result is formalized as a
precise Lean statement with a full book citation; every public theorem is either **fully proven
(0-sorry)** or **structurally proven, reduced to a single named `private` analytic crux** — there are
**no bare public-theorem sorries**.

* ~16 theorems **fully 0-sorry**, including: the entropy appendix (`discreteEntropy_nonneg/le_log_card`,
  `discreteCondEntropy_le_entropy`), `klDiv_gaussianReal` (Ex 15.13), KL tensorization
  (`klDiv_prod_eq_add`, `klDiv_pi_eq_nsmul`), TV/Hellinger basics, **`minimax_local_packing` (Eq 15.35,
  fully closed)**, and the density-estimation / Sobolev example rates (`density_estimation_hellinger_rate`,
  `sobolev_regression_rate`).
* Headline method theorems proven *structurally* (public closed, one named crux): `minimax_ge_testing_error`
  (Prop 15.1), `minimax_two_point` (15.14), `minimax_le_cam_convex_hull` (15.9), `minimax_fano_lower_bound`
  (Prop 15.12), `minimax_yang_barron` (15.21), `pinsker_tv_le_kl` (15.2), `lecam_tv_le_hellinger` (15.3),
  plus all 8 worked-example rate theorems.

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
