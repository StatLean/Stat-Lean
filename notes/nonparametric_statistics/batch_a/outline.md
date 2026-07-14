# Nonparametric statistics, Batch a — outline

Reference: Tsybakov, *Introduction to Nonparametric Estimation* (Springer, 2009), ch. 1.
**The book must NOT be cited in .lean comments** (per `Nonparametric_TODO.md`); Lean docstrings
cite original papers (Rosenblatt/Parzen/Nadaraya/Watson/Stone/Katkovnik/Čencov/Rice/…). This
file is the book↔Lean dictionary; the Tsybakov numbering lives only here.

Area: `StatLean/NonparametricStatistics/` — new area, greenfield (the old ConcentrationInequalities
"KDE uniform rate" milestone was dropped before any code landed; nothing to reuse there).

## Book ↔ Lean dictionary

| Book item | Lean declaration | File |
|---|---|---|
| KDE (1.2), 2-D KDE (1.3) | `kdeData`, `kde`, `kde2Data` | `KernelDensity/Defs.lean` |
| Def 1.1 (bias/variance), MSE (1.4), MISE (1.13) | `kdeBiasAt`, `kdeVarianceAt`, `kdeMseAt`, `kdeMise` | `KernelDensity/Defs.lean` |
| Def 1.2 (Hölder Σ(β,L)); P(β,L) | `MemHolderOn`/`MemHolder`, `IsHolderDensity`; `holderIndex` (strict-floor ℓ = ⌈β⌉₊−1) | `SmoothnessClasses/Defs.lean` |
| Def 1.3 (kernel of order ℓ) | `IsKernelOfOrder` | `KernelDensity/Defs.lean` |
| Def 1.4 (Nikol'skii H(β,L)); P_H(β,L) | `MemNikolski`, `IsNikolskiDensity` | `SmoothnessClasses/Defs.lean` |
| Lemma 1.1 (generalized Minkowski, proof = Lemma A.1) | `lintegral_lintegral_sq_rpow_le` | `ForMathlib/MinkowskiIntegral.lean` |
| Lemma A.2 (L²-translation continuity) | `tendsto_lintegral_sq_sub_translate` | `ForMathlib/TranslationL2.lean` |
| Prop 1.1 (pointwise variance, C₁ = pmax∫K²) | `kde_variance_le` (+ `kde_memLp_two`, `kdeVarianceAt_eq_ofReal_variance`, `kdeMseAt_eq_bias_sq_add_variance`) | `KernelDensity/Variance.lean` |
| Prop 1.2 (pointwise bias, C₂ = (L/ℓ!)∫|u|^β|K|) | `kde_bias_abs_le`, det. core `abs_integral_kernel_taylor_le`, derived integrability `integrable_kernel_mul_holder` | `KernelDensity/Bias.lean` |
| eq (1.9) (uniform bound on P(β,L)) — hidden dependency of Thm 1.1 | `holder_density_uniform_bound` | `KernelDensity/UniformDensityBound.lean` |
| aux bounded order-ℓ kernel (replaces Prop 1.3's Legendre construction; Prop 1.3 itself out of scope) | `exists_bounded_kernel_of_order` (box superposition + Vandermonde) | `KernelDensity/AuxiliaryKernel.lean` |
| Thm 1.1 (pointwise rate n^{−2β/(2β+1)}, ∃C sanctioned) | `kde_pointwise_rate` | `KernelDensity/PointwiseRate.lean` |
| Prop 1.4 (∫σ² ≤ (nh)⁻¹∫K², any density) | `kde_integrated_variance_le` | `KernelDensity/IntegratedVariance.lean` |
| Prop 1.5 (∫b² ≤ C₂²h^{2β} over P_H) | `kde_integrated_sq_bias_le` | `KernelDensity/IntegratedBias.lean` |
| Prop 1.6 (exact asymptotic MISE, proof = Prop A.1) | `kde_exact_mise` (ε·((nh)⁻¹+h⁴) absolute-error form, see below); halves: `kde_integrated_variance_ge`, `kde_integrated_sq_bias_asymptotic`; decomposition (1.14): `kdeMise_eq_integrated` | `KernelDensity/{MISEVariance,MISEBias,ExactMISE}.lean` |
| Taylor–Lagrange / integral remainder tooling | `taylor_lagrange_global`; `taylor_integral_remainder`, `taylor_integral_remainder_sub`; class-level `MemHolder.taylor_remainder_abs_le`(+`_Icc`, growth), `MemNikolski.lintegral_sq_remainder_le` | `ForMathlib/Taylor*.lean`, `SmoothnessClasses/{Holder,Nikolski}Taylor.lean` |
| Def 1.7 (linear estimator; NW estimator) | `IsLinearEstimator`, `nadarayaWatson` | `Regression/Defs.lean` |
| Prop 1.10 (NW = ratio of KDEs) | `nadarayaWatson_eq_kde_ratio` | `Regression/NWKernelRepresentation.lean` |
| Def 1.8 (LP(ℓ), U(u), B_nx, weights (1.65)–(1.67)) | `lpBasis`, `lpObjective`, `IsLPSolution`, `lpMatrix`, `lpRhs`, `lpWeight`, `lpEstimator` | `LocalPolynomial/Defs.lean` |
| Assumptions LP1/LP2/LP3 | `DesignEigenvalueLB` (quadratic-form encoding of λmin ≥ λ₀), `DesignDensityBound`, `KernelBoxed` | `LocalPolynomial/Defs.lean` |
| Prop 1.11 (LP linear) + normal equations (1.66) | `isLinearEstimator_lpEstimator`; `isLPSolution_iff_normal`, `isLPSolution_inv_mulVec`, `isLPSolution_unique`, `lpEstimator_eq_isLPSolution`, `lpMatrix_isSymm`, `lpMatrix_posDef`, inverse bound (1.70) `lpMatrix_inv_mulVec_sq_le` | `LocalPolynomial/Quadratic.lean` |
| Prop 1.12 (polynomial reproduction (1.68)) | `lp_weight_reproduce_monomial`, `lp_weight_sum_one`, `lp_weight_reproduce_poly` (centered-basis form) | `LocalPolynomial/Reproduction.lean` |
| Lemma 1.3 (weight bounds, C* = max{2Kmax/λ₀, 4Kmax·a₀/λ₀}) | `lp_weight_abs_le`, `lp_weight_sum_abs_le`, `lp_weight_eq_zero_of_far` (+ `lpBasis_normSq_le`: ‖U‖² ≤ e) | `LocalPolynomial/WeightBounds.lean` |
| Prop 1.13 (LP bias/variance, q₁ = C*L/ℓ!, q₂ = σ²maxC*²) | `lp_bias_deterministic`, `lp_variance_le`, `lp_mse_le` | `LocalPolynomial/PointwiseRisk.lean` |
| Thm 1.6 (pointwise rate; explicit C = q₁²α^{2β}+q₂/α) | `lp_pointwise_rate` (finite-n, `lpRateConst`) | `LocalPolynomial/PointwiseRisk.lean` |
| Cor 1.2 (L² rate) | `lp_l2_rate` | `LocalPolynomial/L2Risk.lean` |
| Lemma 1.6 (E max η² ≤ log(C₀M)/α₀) | `lintegral_iSup_sq_le_log` (C₀ ≥ 1 derived) | `ForMathlib/MaxExpSquare.lean` |
| Cor 1.3 (Gaussian vectors: E max‖η‖² ≤ 4dσ²log(√2Md)) | `lintegral_iSup_normSq_gaussian_le` (per-coordinate law — weaker hyp than joint Gaussian) | `ForMathlib/MaxExpSquare.lean` |
| Gaussian bricks (E exp(X²/(4σ²)) ≤ √2; weighted sums) | `lintegral_exp_mul_sq_gaussianReal_le`, `hasLaw_sum_mul_gaussianReal` | `ForMathlib/GaussianExpSq.lean` |
| Thm 1.8 (sup-norm rate (log n/n)^{β/(2β+1)}, ∃C sanctioned) | `lp_supnorm_rate`; stochastic term `lp_supnorm_stochastic_le` (grid M = n⁴); increments `lp_weight_lipschitz_sum` | `LocalPolynomial/SupNorm/*.lean` |
| Def 1.9 (projection estimator); trig basis (Ex 1.3); design i/n | `projEstimator`, `coeffEstimator`, `trigBasis` (1-indexed, j/2 frequency), `regularDesign` | `Projection/Defs.lean` |
| Def 1.11 (W(β,L), W^per) | `MemSobolevW`, `MemSobolevWper` (definition-only this batch) | `Projection/Defs.lean` |
| Def 1.12 + ellipsoid Θ(β,Q) (1.90)–(1.91) | `sobolevWeight`, `MemEllipsoid`, `ellipsoidRadius`, class = `seriesFun θ` with `MemEllipsoid` (θ primitive — dodges trig completeness) | `Projection/Defs.lean` |
| Lemma 1.7 (discrete orthonormality) | `trigBasis_discrete_orthonormal`; roots-of-unity sums in `ForMathlib/TrigDiscreteSums.lean`; L² orthonormality `trigBasis_orthonormal` | `Projection/{DiscreteOrthogonality,TrigOrthogonality}.lean` |
| Prop 1.16 (Eθ̂ⱼ = θⱼ+αⱼ; E(θ̂ⱼ−θⱼ)² = σ²/n+αⱼ²) | `coeffEstimator_mean`, `coeffEstimator_sq_error` (+ `seriesFun_abs_le`, `summable_sq_of_summable_abs`) | `Projection/CoefficientRisk.lean` |
| Prop 1.17 (exact MISE decomposition) | `proj_mise_decomposition` (`riemannResidual` = αⱼ, `tailEnergy` = ρ_N) | `Projection/MISEDecomposition.lean` |
| Lemma 1.8 (aliasing bounds) | `riemannResidual_abs_le_tail`, `riemannResidual_abs_le` (explicit `residualConst β Q`); (A)(iii) derived on ellipsoid: `MemEllipsoid.summable_abs` | `Projection/Aliasing.lean` |
| Thm 1.9 (projection MISE rate, ∃C sanctioned) | `proj_sobolev_rate` (finite-n: 3 ≤ n, N = ⌈αn^{1/(2β+1)}⌉₊ ≤ n−1) | `Projection/SobolevRate.lean` |
| tail p-series Σ_{m≥n}m^{−s} | `summable_nat_add_rpow_neg`, `tsum_nat_add_rpow_neg_le` | `ForMathlib/TailSumRpow.lean` |

Out of scope this batch (stretch, do NOT stub): Thm 1.2/1.3 (MISE rate corollaries of Props
1.4+1.5), Prop 1.3 (Legendre kernels), Prop 1.7, Thm 1.7 (regular-design restatement),
Lemmas 1.4/1.5, Prop 1.14 (W^per ↔ Θ, needs trig completeness/Parseval), Prop 1.15, Def 1.10
(density projection), §1.3 Fourier analysis, §1.4 cross-validation.

## Design choices

1. **Risk functionals in ℝ≥0∞** (`∫⁻` + `ENNReal.ofReal`): Bochner junk-0 on non-integrable
   squares would make upper bounds vacuous. Bias (signed) is Bochner; its integrability is
   derived (`integrable_kernel_mul_holder`), never hypothesized in headline theorems.
   Second-moment *hypotheses* also in `∫⁻` form (junk-0 hypotheses would make conclusions false).
2. **iid encoding**: `IsIIDSample P X μ` = `iIndepFun X P` + `∀ i, HasLaw (X i) μ P`
   (`HasLaw` verified on pin; pattern of `ConcentrationInequalities/ClassicalLimits.lean`).
   Density sampling: `densityMeasure p = volume.withDensity (ofReal ∘ p)`.
3. **`holderIndex β = ⌈β⌉₊ − 1`** = the book's strict floor (integer β ↦ β−1). Hölder class
   uses `ContDiffOn` — equivalent to the book's "ℓ-times differentiable" there (Hölder forces
   continuity of f^(ℓ)); Nikol'skii's `ContDiff` is a mild documented strengthening.
4. **LP1 as quadratic-form bound** (`∀ v, λ₀‖v‖² ≤ vᵀBv`), avoiding eigenvalue machinery;
   inverse bound via Cauchy–Schwarz. Closed-form weights (`Matrix.inv`, junk 0 at singular B)
   + minimiser predicate, tied under PosDef — mirrors the OLS/Lasso precedent.
5. **Asymptotic headline statements** are formalized as finite-n bounds with explicit side
   conditions (`h = formula` as an equation hypothesis; `1/(2n) ≤ h`, `h ≤ 1`, `N ≤ n−1`,
   `3 ≤ n` where needed) — these imply the book's limsup forms. Sanctioned ∃C existentials:
   Thm 1.1 (pmax not closed-form), Thm 1.8 (grid/chaining constants), Thm 1.9 (book's C
   unspecified), stochastic/increment intermediates. Everything else has explicit constants.
6. **Prop 1.6** stated in absolute-error form `|MISE − A| ≤ ε((nh)⁻¹ + h⁴)` (∀ε ∃h₀ ∀h<h₀ ∀n≥1)
   — equivalent to the book's (1+o(1)) multiplicative form since A ≍ (nh)⁻¹ + h⁴ (∫K² > 0
   from ∫K = 1; S_K ≠ 0 hypothesis; ∫w² > 0 since a density cannot have w ≡ 0). `MemLp p 2`
   is a documented extra hypothesis (book-silent; derivable in principle via interpolation —
   flagged stretch). AC of p′ encoded by explicit a.e.-derivative witness `w` with
   `deriv p b − deriv p a = ∫_a^b w`.
7. **Projection cluster**: θ is the primitive object, `f := seriesFun θ` — no trigonometric
   completeness needed anywhere. Basis 1-indexed (`trigBasis 0 = 0` inert), sums over
   `Finset.Icc 1 N`, design `regularDesign n i = (i+1)/n`. Assumption (A)(iii) `∑|θ| < ∞` is a
   hypothesis only in the concept-layer files; on the ellipsoid class (Thm 1.9) it is derived.
8. **No Tsybakov citations in .lean**: docstrings use `**Bibliographic comments.**` with
   original sources; hypothesis tags cite the claim + original-source style.

## Dependency DAG / wave schedule (≤3 concurrent; touch-sets pairwise disjoint)

Wave 0 (laptop): all stubs + this ledger on `np/batch-a-stubs`; stub gate on cluster.

| Wave | Item | Branch | Touch-set | Deps | Size |
|---|---|---|---|---|---|
| 1 | A1 | `np/formathlib-taylor` | ForMathlib/{TaylorLagrangeTwoSided, TaylorIntegralRemainder} | — | M |
| 1 | A2 | `np/lp-core` | LocalPolynomial/{Quadratic, Reproduction, WeightBounds} | — | L |
| 1 | A3 | `np/kde-transfer` | KernelDensity/{LawTransfer, Variance}, Regression/NWKernelRepresentation | — | M |
| 2 | B1 | `np/formathlib-analysis` | ForMathlib/{MinkowskiIntegral, TranslationL2, TailSumRpow} | — | L |
| 2 | B2 | `np/smoothness-taylor` | SmoothnessClasses/{HolderTaylor, NikolskiTaylor} | A1 | M |
| 2 | B3 | `np/aux-kernel` | KernelDensity/AuxiliaryKernel | — | L |
| 3 | C1 | `np/kde-bias-rate` | KernelDensity/{Bias, UniformDensityBound, PointwiseRate} | A3, B2, B3 | L |
| 3 | C2 | `np/trig-orthogonality` | ForMathlib/TrigDiscreteSums, Projection/{TrigOrthogonality, DiscreteOrthogonality} | — | M |
| 3 | C3 | `np/gaussian-maximal` | ForMathlib/{GaussianExpSq, MaxExpSquare} | — | M |
| 4 | D1 | `np/kde-integrated` | KernelDensity/{IntegratedVariance, IntegratedBias} | A3, B1, B2 | L |
| 4 | D2 | `np/lp-pointwise` | LocalPolynomial/{PointwiseRisk, L2Risk} | A2, B2 | M |
| 4 | D3 | `np/proj-risk` | Projection/{CoefficientRisk, MISEDecomposition} | C2 | M |
| 5 | E1 | `np/kde-mise` | KernelDensity/{MISEVariance, MISEBias, ExactMISE} | D1, B1 | XL |
| 5 | E2 | `np/lp-supnorm` | LocalPolynomial/SupNorm/{StochasticTerm, Increments, SupNormRate} | A2, C3, D2 | XL |
| 5 | E3 | `np/proj-rate` | Projection/{Aliasing, SobolevRate} | C2, D3, B1 | M/L |

The DAG, not the wave labels, is binding — B3/C2/C3 have no upstream deps and may be pulled
forward when a slot frees. Merge order = wave order; the laptop wires the umbrella at the end.

## Reuse ledger

- `HasLaw` + API (`Mathlib.Probability.HasLaw`) — on pin (used at `ClassicalLimits.lean:135`).
- `ProbabilityTheory.IndepFun.variance_sum`, `variance_sum_pi` — Mathlib, used in-repo.
- `taylor_mean_remainder_lagrange` (`Mathlib.Analysis.Calculus.Taylor`) — base for A1
  (the `uIcc`/`iteratedDeriv` corollary may be post-pin; re-derive if absent).
- `gaussianReal` + `gaussianReal_conv_gaussianReal`, `gaussianReal_map_const_mul`,
  `mgf_gaussianReal` — pin-verified file.
- `Matrix.det_vandermonde(_ne_zero_iff)`, `Matrix.PosDef`, `Matrix.inv` — Mathlib.
- `integral_cos_sq`/`integral_sin_sq`/`integral_cos` (`Analysis.SpecialFunctions.Integrals.Basic`),
  `Finset.geom_sum_eq`, `Complex.exp_int_mul_two_pi_mul_I` — for C2.
- `MemLp` (`MeasureTheory.Function.LpSeminorm.Defs`); `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`
  (candidate for B1 TranslationL2); `ENNReal.lintegral_mul_le_Lp_mul_Lq` (candidate for B1
  Minkowski) — re-verify names on pin at closure time.
- Fallback noise route for E2 if literal Gaussianity stalls: `ConcentrationInequalities.Orlicz` /
  `SubGaussian` toolkits (cross-area import precedented by HDS) — constants change, document.
