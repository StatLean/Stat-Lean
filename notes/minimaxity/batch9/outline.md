# Batch 9 — Minimaxity (Wainwright Ch. 15): outline

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*
(Cambridge, 2019), Ch. 15. PDF `ref/Wainwright/Wainwright_minimaxity.pdf` (39 pp).
**Integration branch.** `mmx/batch9` (off `main`). Per-unit proof branches `mmx/<unit>`.
**Pin.** `leanprover/lean4:v4.29.1`. Cite tag: `Wainwright §15.x`.

## Keystone encoding decision (the big reuse)

Mathlib **already has** the decision-theoretic risk framework in
`Mathlib/Probability/Decision/Risk/{Defs,Basic}.lean` (`ProbabilityTheory`):

* `minimaxRisk ℓ P = ⨅_κ ⨆_θ ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)` — Wainwright Eq. (15.1)/(15.2).
* `bayesRisk ℓ P π = ⨅_κ avgRisk ℓ P κ π` (avg over prior `π`).
* Estimators = Markov kernels `Kernel 𝓧 𝓨` (randomized; deterministic = `Kernel.deterministic`).
* `bayesRisk_le_minimaxRisk`, `iSup_bayesRisk_le_minimaxRisk` — **Bayes ≤ minimax** (any prior).
* `bayesRisk_le_bayesRisk_comp` / `_map` — **data-processing inequality** (DPI).
* `bayesRisk_const`, `bayesRisk_le_iInf`, boundedness, subsingleton lemmas.

`Defs.lean` is therefore a *thin* Wainwright layer:
* `distortionLoss Φ g θ y := Φ (edist (g θ) y)` — loss `Φ∘ρ`, `ρ = edist` (`PseudoEMetricSpace Ω`;
  Wainwright's semimetric = pseudo-(e)metric, footnote 1).
* `minimaxRiskDist Φ g P := minimaxRisk (distortionLoss Φ g) P` — `M(θ(𝒫); Φ∘ρ)`.
* `zeroOneLoss M`, `uniformPrior M`, `multiwayTestingError Q := bayesRisk (zeroOneLoss M) Q (uniformPrior M)`
  — the M-ary test error `inf_ψ ℚ[ψ(Z)≠J]` (§15.1.2).
* `mixture Q := Q ∘ₘ uniformPrior M` — `Q̄ = (1/M)Σ P_{θʲ}` (Eq. (15.30)).
* `IsSeparatedFamily g θfam δ := ∀ j≠k, 2δ ≤ edist (g (θfam j)) (g (θfam k))` — 2δ-separated set.

**Prop 15.1 chain (EstimationToTesting):** restrict `minimaxRisk` over the full `Θ` to the
finite separated subfamily `θfam : Fin M → Θ` (sup over a subset is smaller) → `bayesRisk`
(uniform prior) ≤ that restricted minimax (avg ≤ max) → geometric step (2δ-separation +
triangle ineq, Fig 15.1): `Φ(edist (g θʲ) y) ≥ Φ(δ)·𝟙[argmin-test errs]` → `Φ(δ)·testingError`.

## Reuse map

| Need | Reuse | Where |
|---|---|---|
| minimax/Bayes risk, DPI, Bayes≤minimax | `minimaxRisk`,`bayesRisk`,`avgRisk`,`bayesRisk_le_*` | `Mathlib/Probability/Decision/Risk/*` |
| KL engine + tensorization (15.11) | `klDiv`, `klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/*` |
| Hellinger tensorization (15.12) | `hellinger_affinity_pi_eq_pow`, `hellinger_product_eLpNorm_le_sqrt_n_per_sample`, `one_sub_pow_le_nsmul_one_sub` | `StatLean/AsymptoticStatistics/ForMathlib/HellingerProduct.lean` |
| metric entropy | `Metric.coveringNumber`/`packingNumber` | `Mathlib/Topology/MetricSpace/CoveringNumbers.lean` |
| Gaussian measures | `gaussianReal`,`multivariateGaussian` | `Mathlib/Probability/Distributions/Gaussian/*` |
| binary entropy | `Real.binEntropy` | Mathlib SpecialFunctions |
| uniform prior | `PMF.uniformOfFintype …|>.toMeasure` | `Mathlib/Probability/Distributions/Uniform.lean` |
| llr / rnDeriv | `MeasureTheory.llr`, `Measure.rnDeriv`, `withDensity` | Mathlib |

Build gaps: TV (½∫|p−q|) + variational rep (Ex 15.1); squared-Hellinger book def; Pinsker
(Lemma 15.2); Le Cam ineq (Lemma 15.3); Gaussian KL (Ex 15.13); Gaussian max-entropy (Lemma 15.17);
Ch.5 packing/entropy (Hamming/sphere/sparse/Sobolev).

## Unit DAG (30 units; ● mod, ◆ hard, ◆◆ research)

```
Defs[laptop]
 ├─ ForMathlib/Entropy ● ───────────────┐
 ├─ ForMathlib/TotalVariation ●         │
 ├─ ForMathlib/KLDivergence ●           │
 ├─ ForMathlib/HellingerDivergence ●    │
 ├─ ForMathlib/Packing/HammingPacking ◆ │
 ├─ ForMathlib/Packing/SpherePacking ◆  │
 ├─ ForMathlib/Packing/SparsePacking ◆  │
 └─ EstimationToTesting ● (Prop 15.1; Defs + DPI/Bayes≤minimax)
      ForMathlib/PinskerInequality ◆ (KL,TV; Lemma 15.2)
      ForMathlib/LeCamInequality ◆ (Hellinger,TV; Lemma 15.3)
      ForMathlib/FanoInequality ◆ (Entropy; Eq 15.61⇒15.31)
      ForMathlib/GaussianKL ◆ (Ex 15.13)
      ForMathlib/GaussianMaxEntropy ◆◆ (Lemma 15.17)
      ForMathlib/Packing/SobolevEntropy ◆◆ (Ex 5.12)
      Fano/MutualInformation ● (KL,Entropy; 15.29/30/34)
        LeCam/TwoPoint ● (TV,E2T; 15.13/14)
        LeCam/ConvexHull ◆ (TV; Lemma 15.9)
        LeCam/Functional ◆ (LeCamIneq,TwoPoint; modulus 15.17, Cor 15.6)
        Fano/FanoLowerBound ● (FanoIneq,E2T,MI; Prop 15.12)
          Fano/LocalPacking ◆ (FanoLB,Packing; 15.35)
          Fano/YangBarron ◆ (MI; Lemma 15.21)
            Examples/{GaussianLocation,UniformLocation,LipschitzDensity,
              QuadraticFunctional,LinearRegression,DensityEstimation,PCA,Sobolev}
```

## Headline declarations (website + axiom audit)

`minimaxRiskDist`, `minimax_ge_testing_error` (Prop 15.1), `pinsker_tv_le_kl` (15.2),
`lecam_tv_le_hellinger` (15.3), `minimax_two_point` (15.14), `minimax_le_cam_convex_hull` (15.9),
`minimax_fano_lower_bound` (15.12), `minimax_local_packing` (15.35), `minimax_yang_barron` (15.21),
+ each example rate theorem.

## Status (Wave 0 — stubbing)

Umbrella `StatLean.Minimaxity` stub-gates **green** on `mmx/batch9` (pin v4.29.1). 14 files drafted;
11 confirmed green (`Build completed successfully`, 16 sorries), 3 gating:

| File | Stub-gate | Headline decls |
|---|---|---|
| `Defs` | ✅ 0 sorry | `minimaxRiskDist`, `multiwayTestingError`, `mixture`, `IsSeparatedFamily` |
| `ForMathlib/KLDivergence` | ✅ | `klDiv_prod_eq_add`, `klDiv_pi_eq_nsmul`, `sum_klDiv_mixture_le` |
| `ForMathlib/TotalVariation` | ✅ | `tvDist`, `tvDist_eq_half_lintegral`, `one_sub_tvDist_eq_iInf` |
| `ForMathlib/HellingerDivergence` | ✅ | `sqHellinger`, `sqHellinger_le_two`, `sqHellinger_pi_le_nsmul` |
| `ForMathlib/PinskerInequality` | ✅ | `pinsker_tv_le_kl` (15.2) |
| `ForMathlib/LeCamInequality` | ✅ | `lecam_tv_le_hellinger` (15.3) |
| `ForMathlib/Packing/HammingPacking` | ✅ | `exists_hamming_packing` (Ex 5.3) |
| `ForMathlib/Packing/SpherePacking` | ✅ | `exists_sphere_packing` (Ex 5.8) |
| `EstimationToTesting` | ✅ | `minimax_ge_testing_error` (Prop 15.1) |
| `Fano/MutualInformation` | ✅ | `mutualInformation`, `mutualInformation_le_avg_pairwise_kl` |
| `ForMathlib/Packing/SparsePacking` | ⏳ | `exists_sparse_packing` (Ex 5.8) |
| `LeCam/TwoPoint` | ⏳ | `binary_testingError_eq_tvDist` (15.13), `minimax_two_point` (15.14) |
| `Fano/FanoLowerBound` | ⏳ | `fano_inequality` (15.31), `minimax_fano_lower_bound` (Prop 15.12) |

**Validated reuse:** `ProbabilityTheory.minimaxRisk`/`bayesRisk` (+ `bayesRisk_le_minimaxRisk`, DPI),
`klDiv` (arg-order matches Wainwright `D(Q‖P)`), StatLean `HellingerProduct.*`, `PMF.uniformOfFintype`.

**Encoding decisions locked:** measurable-space binders are **instance-implicit** `[…]` (so
`minimaxRiskDist`'s `Ω` measurable space resolves by synthesis — regular implicit `{…}` was
unsynthesizable). `Fano/FanoLowerBound` carries `fano_inequality` (KL-MI form); `ForMathlib/Entropy`
will hold the appendix (Def 15.24/25, 15.60a-e) used by its proof.

**Remaining to stub (Wave 0):** `ForMathlib/Entropy` (appendix), `ForMathlib/GaussianKL` (Ex 15.13),
`ForMathlib/GaussianMaxEntropy` ◆◆ (15.17), `ForMathlib/Packing/SobolevEntropy` ◆◆ (Ex 5.12),
`LeCam/{ConvexHull,Functional}`, `Fano/{LocalPacking,YangBarron}`, `Examples/*` (8).
