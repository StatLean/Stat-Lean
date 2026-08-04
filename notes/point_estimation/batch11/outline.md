# PointEstimation Batch 11 — outline & book↔Lean dictionary

Reference: Lehmann & Casella, *Theory of Point Estimation*, 2nd ed. (TPE2), `ref/Point_Estimation/Point_estimation.pdf` (PDF page = book page + 27); plus Lehmann & Romano, *Testing Statistical Hypotheses*, 4th ed. (TSH4 — file `ref/Hypothesis_Tests/TSH2.pdf` despite the name), §2.6 only (PDF ≈ book + 14).

**Citation rule (binding, same as NonparametricStatistics): the textbooks are NEVER named in `.lean` comments/docstrings.** Cite primary sources in `**Bibliographic comments.**` (Fisher 1922, Neyman 1935, Halmos–Savage 1949, Bahadur 1957, Lehmann–Scheffé 1950/1955, Rao 1945, Cramér 1946, Blackwell 1947, Basu 1955, Dynkin 1951, Pitman 1939, Stein 1959/1981, Gauss 1821/Markov). Book numbering lives ONLY here.

## Target ledger (73 items)

Status: STUB = statement committed, sorry body; REAL = proof closed; DEBT = named documented sorry kept deliberately.

### §1.5 Exponential families (PDF 50–59)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Eq (5.1) | general s-dim exp family exp[Σηᵢ(θ)Tᵢ−B(θ)]h dμ | | |
| Eq (5.2) | canonical form exp[⟪η,T⟫−A(η)]h dμ; natural parameter space | | |
| Def 5.2 | identifiability | | |
| Thm 5.8 | ∫f·e^{⟪η,T⟫}h dμ continuous, C^∞ on interior; differentiate under ∫ | | |
| Thm 5.10 | mgf/cgf of T = e^{A(η+u)−A(η)} / A(η+u)−A(η) near 0 | | |
| Lem 5.15 | Stein identity (1-D integration by parts, boundary terms vanish) | | |
| Thm 5.17 | natural statistic T itself exp-family distributed | | |

### §1.6 Sufficiency (PDF 59–70) + TSH4 §2.6 (PDF 61–63)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Def (p.32/35) | sufficiency: conditional distribution of X given T θ-free | | |
| Thm 6.1 | sufficiency ⇒ risk-equal randomized estimator through T | | |
| Def (p.37) | minimal sufficiency | | |
| Thm 6.12 | likelihood-ratio vector minimal sufficient (finite family, common support) | | |
| Cor 6.13 | U sufficient iff density ratios factor through U | | |
| Cor 6.16 | canonical exp family: T minimal sufficient (rank condition) | | |
| Def (p.42) | completeness (and bounded completeness) | | |
| Thm 6.21 | Basu: complete sufficient T ⟂ ancillary V | | |
| Thm 6.22 | full-rank exp family ⇒ T complete | | |
| TSH Thm 2.6.1 | θ-free regular conditional distribution given sufficient T (Euclidean/standard Borel) | | |
| TSH Thm 2.6.2 | Halmos–Savage: T sufficient ⟺ dPθ/dλ factors through T, λ=Σcᵢ Pθᵢ | | |
| TSH Cor 2.6.1 | Fisher–Neyman factorization pθ = gθ∘T · h | | |

### Ch 2 §2.1 UMVU (PDF 110–115)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Def 1.1 | unbiased estimator | | |
| Lem 1.4 | unbiased estimators = δ₀ − {unbiased estimators of 0} | | |
| Def 1.6 | UMVU | | |
| Thm 1.7 | UMVU ⟺ uncorrelated with every unbiased estimator of 0 | | |
| Lem 1.10 | complete sufficient T: unique unbiased function of T | | |
| Thm 1.11 | Lehmann–Scheffé: min risk for every convex loss | | |
| Cor 1.12 | full-rank exp-family specialization | | |

### Ch 2 §2.5 information inequality (PDF 140–150)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 5.1 | covariance characterization via unbiased estimators of 0 | | |
| Thm 5.4 | exp-family Fisher information = A″ | | |
| Thm 5.8 | additivity of Fisher information under independence | | |
| Thm 5.10 | Cramér–Rao: var δ ≥ g′(θ)²/I(θ) | | |
| Thm 5.12 | attainment ⟺ exponential family, δ affine in T | | |
| Thm 5.15 | family-side regularity version (holds for all δ with Eδ²<∞) | | |

### Ch 2 §2.6 multiparameter (PDF 151–154)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 6.1 | covariance-matrix inequality (general ψ) | | |
| Thm 6.2 | exp-family Fisher information matrix | | |
| Thm 6.6 | multiparameter Cramér–Rao (∂g)ᵀI(θ)⁻¹(∂g) | | |

### Ch 3 §3.1 location equivariance (PDF 176–185)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Def 1.2 | location-invariant estimation problem | | |
| Def 1.3 | location-equivariant estimator | | |
| Thm 1.4 | equivariant ⇒ constant bias/risk/variance | | |
| Def 1.5 | MRE estimator | | |
| Lem 1.6 | δ equivariant ⟺ δ=δ₀−u, u translation-invariant | | |
| Lem 1.7 | u translation-invariant ⟺ function of differences (n≥2) | | |
| Thm 1.8 | general equivariant δ = δ₀ − v(y) | | |
| Thm 1.10 | MRE via conditional minimization given differences | | |
| Cor 1.11 | existence under convex non-monotone ρ; uniqueness if strict | | |
| Cor 1.12 | squared error: v* = E₀[δ₀|y] (Pitman); absolute error: median | | |
| Cor 1.14 | n=1, bounded loss: explicit MRE | | |
| Thm 1.17 | X̄ MRE characterization | | |
| Thm 1.20 | Pitman estimator closed form (ratio of integrals) | | |
| Lem 1.23 | auxiliary identity for risk-unbiasedness | | |
| Def 1.24 | risk-unbiased estimator | | |
| Thm 1.27 | MRE (convex even loss) ⇒ risk-unbiased | | |

### Ch 3 §3.2 the principle of equivariance (PDF 185–193)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Def 2.1 | G-invariant model | | |
| Def 2.4 | invariant loss (L(ḡθ,g*d)=L(θ,d)) | | |
| Def 2.5 | equivariant estimator δ(gx)=g*δ(x) | | |
| Thm 2.7 | risk invariant under induced Ḡ | | |
| Cor 2.8 | Ḡ transitive ⇒ constant risk | | |
| Def 2.10 | orbits of Ḡ | | |
| Cor 2.13 | risk constant on orbits | | |
| Thm 2.15 | transitive Ḡ + commutative G* ⇒ MRE exists (structure) | | |
| Thm 2.17 | power-series family application | | |

### Ch 3 §3.3 scale (PDF 195–201)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 3.1 | scale-equivariant δ = δ₀/w(z) | | |
| Thm 3.3 | scale-MRE by conditional minimization | | |
| Cor 3.4 | convex ρ(v)=γ(eᵛ) form | | |
| Cor 3.8 | explicit MRE of τʳ (ratio of conditional expectations) | | |
| Thm 3.17 | location-scale MRE characterization | | |

### Ch 3 §3.4 normal linear models (PDF 205–212)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 4.3 | canonical model: Yᵢ UMVU/MRE for ηᵢ; c·Sʳ for σʳ | | |
| Thm 4.4 | UMVU of Σγᵢηᵢ and σ² | | |
| Cor 4.5 | equivariance of the canonical estimators | | |
| Thm 4.8 | least-squares projection UMVU/MRE (subspace mean) | | |
| Thm 4.10 | general s-dim subspace extension | | |
| Thm 4.12 | Gauss–Markov (least squares UMVU among linear) | | |
| Cor 4.13 | BLUE | | |
| Thm 4.14 | regression-coefficient form + covariance | | |

## Work items / waves

(filled after design review — see status.md)
