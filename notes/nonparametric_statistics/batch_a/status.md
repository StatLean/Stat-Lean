# Nonparametric statistics, Batch a — status

Last update: 2026-07-14 (ALL WAVES CLOSED — batch 0-sorry; full-lib build + axiom sweep in
final gate).

E-wave + fixes outcomes:
- lp-core-fix: both renegotiated Quadratic debts CLOSED under the `0<h` amendment
  (completing-the-square, `n ≥ 1` derived from PosDef). LP Quadratic fully real.
- E1 `np/kde-mise` (3 sessions): MISEVariance exact lower bound (Young/Minkowski convolution
  L²), MISEBias closed incl. `stepC_bound` (double Minkowski + nested dominated convergence
  on the translation modulus — hardest lemma of the batch), ExactMISE assembly (3 drift
  errors fixed in a follow-up micro-session). **Prop 1.6 CLOSED.**
  Process note: one E1 gate ran red (3 assembly errors) and was merged prematurely by a bad
  `&&`-chain (tail success masked rc=1); fixed forward by E1C, whose gate was verified green
  before merging. No red state ever reached main.
- E2 `np/lp-supnorm` (2 sessions): Increments ℓ¹-Lipschitz (case-split crude/smooth +
  resolvent), StochasticTerm (n⁴ grid, Gaussian weighted-sum law + exp-square maximal bound,
  ℓ¹-noise increment), SupNormRate (bias/stochastic split + rpow bandwidth substitution).
  **Thm 1.8 CLOSED.**
- E3 `np/proj-rate`: ellipsoid→ℓ¹ (AM-GM + p-series), aliasing rate (Cauchy–Schwarz on the
  tail + tail p-series, explicit `residualConst`), **Thm 1.9 CLOSED** (three-term assembly;
  Σ|θ| DERIVED on the ellipsoid).

Waves 2–4 outcomes (all gate-verified 0-sorry in their touch-sets, merged):
- B1 Minkowski-L² (duality + spanning-set truncation) / translation-L² (3ε via
  compact-support density) / p-series tails. B2 Hölder/Nikolskii Taylor (incl. a private
  two-sided Icc Taylor–Lagrange via Cauchy MVT). B3 aux kernel (box superposition +
  Vandermonde). C1 KDE bias + uniform density bound + **Thm 1.1 pointwise rate CLOSED**.
  C2 trig discrete sums (roots of unity) + L²/discrete orthonormality (9-case).
  C3 Gaussian exp-square moment (exact Gaussian integral), weighted-sum law (conv induction),
  max-of-squares log-bounds (tangent-line trick, C₀ ≥ 1 derived). D1 **Prop 1.4 + Prop 1.5
  CLOSED** (a.e.-x Tonelli discipline; no boundedness of p anywhere). D2 **Thm 1.6 + Cor 1.2
  CLOSED** (measurable-in-t weights via det/adjugate for the Tonelli swap). D3 **Prop 1.16 +
  Prop 1.17 CLOSED** (exact MISE decomposition; tail-function orthogonality via integral_tsum).

Wave log:
- Stub gate: green-with-sorries (77 planned) after 2 import-fix rounds (Lebesgue volume
  instance; pin paths Measure.Prod / Pow.NNReal / Moments.Variance).
- A1 `np/formathlib-taylor`: CLOSED 0-sorry (uses Mathlib
  `taylor_mean_remainder_lagrange_iteratedDeriv`, reflection for two-sidedness; integral
  remainder by induction + IBP). Gate: fresh build OK, diff ⊆ touch-set. Merged.
- A3 `np/kde-transfer`: CLOSED 0-sorry (law transfer, kde mean formula, MemLp₂,
  variance ≤ C₁/(nh), MSE decomposition, NW = kde ratio). Gate OK. Merged.
- A2 `np/lp-core`: 13/15 closed; **statement renegotiation** — subagent found
  `isLPSolution_iff_normal` (mpr) and `isLPSolution_inv_mulVec` FALSE as stated for
  `n·h < 0` (PosDef `B_t` but concave objective; counterexample `n=1, ℓ=0, h<0, K<0`).
  Laptop added `(hh : 0 < h)` LEAN-ONLY to both (book always has `h > 0`); 2 named debts
  remain for `np/lp-core-fix`. Reproduction avoided the flawed lemmas (pure normal-equations
  algebra) — no taint. Gate OK (exactly the 2 agreed debts). Merged.

## Theorem / unit ledger

All units stubbed statement-first on `np/batch-a-stubs` (41 files; 5 sorry-free Defs). Status
key: STUB (sorry), REAL (closed, verified on cluster), — (n/a).

| Unit (book ref) | Lean name | Status |
|---|---|---|
| Prop 1.1 | `kde_variance_le` (+3 support lemmas) | STUB |
| Prop 1.2 | `kde_bias_abs_le` (+2) | STUB |
| eq (1.9) | `holder_density_uniform_bound` | STUB |
| aux kernel | `exists_bounded_kernel_of_order` | STUB |
| Thm 1.1 | `kde_pointwise_rate` | STUB |
| Prop 1.4 | `kde_integrated_variance_le` | STUB |
| Lemma 1.1 | `lintegral_lintegral_sq_rpow_le` | STUB |
| Prop 1.5 | `kde_integrated_sq_bias_le` | STUB |
| Lemma A.2 | `tendsto_lintegral_sq_sub_translate` | STUB |
| Prop 1.6 | `kde_exact_mise` (+3: var ≥, bias asympt, decomposition) | STUB |
| Taylor bricks | `taylor_lagrange_global`, `taylor_integral_remainder`(+`_sub`) | STUB |
| Hölder/Nikolskii Taylor | `MemHolder.taylor_remainder_abs_le`(+Icc, growth, deriv), `MemNikolski.lintegral_sq_remainder_le` | STUB |
| Def 1.7 / Prop 1.10 | `nadarayaWatson_eq_kde_ratio` | STUB |
| Def 1.8 / Prop 1.11 / (1.66) | `Quadratic.lean` (8 lemmas) | STUB |
| Prop 1.12 | `Reproduction.lean` (3 lemmas) | STUB |
| Lemma 1.3 | `WeightBounds.lean` (4 lemmas) | STUB |
| Prop 1.13 / Thm 1.6 | `lp_bias_deterministic`, `lp_variance_le`, `lp_mse_le`, `lp_pointwise_rate` | STUB |
| Cor 1.2 | `lp_l2_rate` | STUB |
| Lemma 1.6 / Cor 1.3 | `lintegral_iSup_sq_le_log`, `lintegral_iSup_normSq_gaussian_le` | STUB |
| Gaussian bricks | `lintegral_exp_mul_sq_gaussianReal_le`, `hasLaw_sum_mul_gaussianReal` | STUB |
| Thm 1.8 | `lp_supnorm_rate` (+ stochastic, increments) | STUB |
| Lemma 1.7 | `trigBasis_discrete_orthonormal` (+4 trig-sum bricks, +2 orthonormality) | STUB |
| Prop 1.16 | `coeffEstimator_mean`, `coeffEstimator_sq_error` (+2 helpers) | STUB |
| Prop 1.17 | `proj_mise_decomposition` | STUB |
| Lemma 1.8 | `riemannResidual_abs_le(_tail)`, `MemEllipsoid.summable_abs` | STUB |
| Thm 1.9 | `proj_sobolev_rate` | STUB |
| tail p-series | `summable_nat_add_rpow_neg`, `tsum_nat_add_rpow_neg_le` | STUB |

## Honesty: derived, not laundered

- `pmax` (uniform bound over P(β,L)) — NOT a hypothesis of Thm 1.1; derived via
  `holder_density_uniform_bound` ← `exists_bounded_kernel_of_order`.
- Integrability of `u ↦ K(u)·p(x₀+uh)` — derived (`integrable_kernel_mul_holder`).
- `∑|θⱼ| < ∞` — hypothesis only at concept level (Props 1.16/1.17); DERIVED on the ellipsoid
  in Thm 1.9 (`MemEllipsoid.summable_abs`).
- `C₀ ≥ 1` in Lemma 1.6 — derived (Jensen), not assumed.
- Noise integrability (mean-zero Bochner hypotheses meaningful) — forced by `∫⁻`-form second
  moments.
- Documented EXTRA hypotheses vs book: `MemLp p 2` in Prop 1.6 (variance lower bound);
  `ContDiff` (vs a.e. differentiability) in `MemNikolski`; measurability side conditions
  (LEAN-ONLY tagged).

## Book-vs-Lean constants

| Quantity | Book | Lean | Note |
|---|---|---|---|
| C₁ (Prop 1.1) | pmax∫K² | `kdeVarianceConst` — same | exact |
| C₂ (Prop 1.2/1.5) | (L/ℓ!)∫\|u\|^β\|K\| | `kdeBiasConst` — same | exact |
| C* (Lemma 1.3) | max{2Kmax/λ₀, 4Kmax·a₀/λ₀} | `lpWeightConst` — same | uses ‖U(z)‖² ≤ e ≤ 4 |
| q₁, q₂ (Prop 1.13) | C*L/ℓ!, σ²maxC*² | `lpBiasConst`, `lpVarConst` — same | exact |
| Thm 1.6 C | unspecified | `lpRateConst = q₁²α^{2β} + q₂/α` | explicit (stronger than book) |
| Lemma 1.6/Cor 1.3 | log(C₀M)/α₀; 4dσ²log(√2Md) | same | exact |
| Lemma 1.8 C_{β,Q} | unspecified | `residualConst = 2√Q·√(2β/(2β−1))·3^{β−1/2}` (n ≥ 3) | explicit |
| p-series tail | 1/(s−1) sharp | `s/(s−1)` | deliberately generous |
| Thm 1.1 / 1.8 / 1.9 C | unspecified | ∃C | sanctioned existentials |
| Prop 1.6 o(1) | multiplicative | absolute ε((nh)⁻¹+h⁴) | equivalent; see outline §6 |
| Thm 1.8 grid | M = n² | M = n⁴ (proof-internal) | generous, harmless |

## Axioms

Gate per merged item: `#print axioms` = `[propext, Classical.choice, Quot.sound]` only.
Nothing merged yet.

## Parallelization plan/outcome

See outline.md wave table. Wave 0 stubs: 2026-07-14. Stub gate: pending. Waves 1–5: pending.
