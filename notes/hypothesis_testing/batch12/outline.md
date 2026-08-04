# HypothesisTesting Batch 12 — outline & book↔Lean dictionary

Reference: Lehmann & Romano, *Testing Statistical Hypotheses*, **4th edition** (2022) — file `ref/Hypothesis_Tests/TSH2.pdf` (misnamed; it is the 4th ed., 1016 PDF pages). PDF↔printed offset drifts: +14 (Ch 3), +13 (Ch 4/6), +9 (Ch 14), +8 (Ch 16), +7 (Ch 17), +6 (Ch 18).

**Citation rule (binding): the textbook is NEVER named in `.lean` comments/docstrings.** Primary sources for `**Bibliographic comments.**`: Neyman–Pearson 1933, Lehmann 1947–55, Hunt–Stein 1946, Stein 1956, Fisher 1935, Pitman 1937, Hoeffding 1952, Dwass 1957, Kolmogorov 1933, Smirnov 1948, Massart 1990 (DKW), Pearson 1900, Neyman 1937 (smooth tests), Wald 1943, Rao 1948, Wilks 1938, Le Cam 1960, Efron 1979, Bickel–Freedman 1981, Singh 1981, Beran 1984, Hall 1992, Romano 1989/1990. Book numbering ONLY here.

## Target ledger (73 numbered items + prose definitions)

Prose definitions that MUST also be formalized (unnumbered in book): randomized test / critical function, size/level/power, MP/UMP, MLR, similar test, Neyman structure, unbiased test, maximal invariant, almost invariance, UMP invariant/unbiased, randomization distribution, bootstrap estimate.

### Ch 3 UMP tests (PDF 80–110)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 3.2.1 | Neyman–Pearson fundamental lemma (existence + sufficiency + necessity) | | |
| Cor 3.2.1 | strict unbiasedness α<β unless P₀=P₁ | | |
| Lem 3.3.1 | p-value super-uniformity (nested rejection regions) | | |
| Thm 3.4.1 | MLR: UMP one-sided test exists | | |
| Cor 3.4.1 | 1-param exp family has MLR ⇒ UMP one-sided | | |
| Thm 3.4.2 | one-sided tests essentially complete class | | |
| Lem 3.4.1 | stochastic dominance quantile coupling | | |
| Lem 3.4.2 | MLR ⇒ E_θψ monotone for monotone ψ | | |
| Thm 3.5.1 | test ↔ confidence set duality | | |
| Cor 3.5.1 | uniformly most accurate one-sided bounds (MLR) | | |
| Thm 3.6.1 | generalized NP lemma (m constraints) | | |
| Cor 3.6.1 | test with prescribed E_iφ = α exists | | |
| Lem 3.6.1 | Lagrangian sufficiency | | |
| Thm 3.7.1 | exp family UMP two-sided (C₁<T<C₂) | | |
| Lem 3.7.1 | two-sided comparison/uniqueness | | |
| Thm 3.8.1 | least favorable distributions | | |
| Cor 3.8.1 | least favorable Λ identification | | |

### Ch 4 UMPU §4.1–4.4, 4.9 (PDF 140–154)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Lem 4.1.1 | continuous power + UMP-on-boundary ⇒ UMPU | | |
| Thm 4.3.1 | full-rank exp family: family of T complete (imported from PointEstimation) | | |
| Thm 4.3.2 | Neyman structure ⟺ bounded completeness of P^T | | |
| Thm 4.4.1 | UMPU φ₁–φ₄ for multiparameter exp family (conditioning on T) | | |
| Lem 4.4.1 | canonical (U,T) form | | |

### Ch 6 invariance (PDF 255–297)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Lem 6.1.1 | family-preserving transformations form a group | | |
| Thm 6.2.1 | invariant ⟺ factors through maximal invariant | | |
| Thm 6.2.2 | stepwise maximal invariants | | |
| Thm 6.3.1 | finite group, transitive Ḡ: UMP invariant test (orbit-avg LR) | | |
| Thm 6.3.2 | invariant statistic's law depends only on maximal invariant of Ḡ | | |
| Thm 6.5.1 | almost invariant ⟹ equivalent invariant (conditions) | | |
| Cor 6.5.1 | UMP invariant ⇒ UMP almost-invariant | | |
| Lem 6.5.1 | boundedly complete sufficient T: power invariant ⟺ almost invariant | | |
| Thm 6.5.2 | UMP a.i. based on T is UMP among v(θ)-power tests | | |
| Thm 6.5.3 | sufficiency-then-invariance reduction legitimate | | |
| Thm 6.6.1 | unique UMPU + UMP a.i. ⇒ coincide | | |
| Thm 6.7.1 | exp family: closed convex acceptance region d-admissible | | |
| Cor 6.7.1 | + α-admissibility | | |
| Thm 6.7.2 | Bayes ⇒ admissible (Stein-type) | | |
| Lem 6.7.1 | scale-mixture integral identity | | |
| Lem 6.10.1 | symmetry/sign-change identity | | |
| Lem 6.11.1 | equivariant confidence sets ↔ invariant acceptance regions | | |

### Ch 14 §14.4 likelihood trinity (PDF 690–701)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 14.4.1 | asymptotically-linear estimator: limit under θ₀+h/√n (contiguity) | | |
| Cor 14.4.1 | score vector → N(I(θ₀)h, I(θ₀)) under local alternatives | | |
| Thm 14.4.2 | Wald ≍ Rao score ≍ LR, asymptotically χ² | | |

### Ch 16 goodness of fit §16.2–16.4 (PDF 783–807)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 16.2.1 | KS pointwise consistency | | |
| Thm 16.2.2 | KS uniform power, √n·d_K ≥ εₙ→∞ | | |
| Thm 16.2.3 | KS no local power at o(n^{-1/2}) | | |
| Thm 16.3.1 | Pearson χ² → χ²_k (simple null, multinomial) | | |
| Thm 16.3.2 | χ² test asymptotic maximin bound | | |
| Lem 16.3.1 | noncentral χ² tail function M(k,h) | | |
| Thm 16.4.1 | Neyman smooth test asymptotically maximin (fixed k) | | |
| Lem 16.4.1 | multivariate Berry–Esseen-type bound | | |
| Thm 16.4.2 | smooth test, kₙ→∞: asymptotically normal | | |

### Ch 17 permutation/randomization (PDF 839–861)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Def 17.2.1 | randomization hypothesis (gX =d X under H₀) | | |
| Thm 17.2.1 | randomization test EXACT level α (finite group) | | |
| Thm 17.2.2 | conditional-on-orbit law = randomization distribution | | |
| Thm 17.2.3 | asymptotics of randomization distribution (triangular array) | | |
| Thm 17.2.4 | sign-change randomization asymptotically normal | | |
| Thm 17.3.1 | two-sample permutation CLT | | |
| Thm 17.3.2 | Slutsky for randomization distributions | | |
| Thm 17.3.3 | studentized two-sample permutation test valid | | |
| Lem 17.4.1 | multivariate quadratic-form building block | | |
| Lem 17.4.2 | joint convergence under two independent assignments | | |
| Lem 17.4.3 | independent χ² pair limit | | |

### Ch 18 bootstrap §18.1–18.5 (PDF 877–897)
| Book | Content | Lean name | Status |
|---|---|---|---|
| Thm 18.3.1 | general bootstrap consistency (C_P triangular-array criterion) | | |
| Thm 18.3.2 | uniform version + quantile consistency | | |
| Cor 18.3.1 | bootstrap test local power | | |
| Thm 18.3.3 | nonparametric mean bootstrap | | |
| Thm 18.3.4 | studentized mean bootstrap-t | | |
| Lem 18.3.1 | first-absolute-moment convergence tool | | |
| Thm 18.3.5 | multivariate bootstrap | | |
| Thm 18.3.6 | smooth functions of means | | |
| Thm 18.4.1 | Edgeworth expansion (studentized) — book cites Hall 1992, no proof | | |
| Thm 18.4.2 | uniform Edgeworth, bootstrap O(n⁻¹) accuracy — book cites Hall 1992, no proof | | |
| Thm 18.5.1 | bootstrap hypothesis testing asymptotic level α | | |

## Work items / waves

(filled after design review — see status.md)
