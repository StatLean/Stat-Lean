import type { CategoryId } from "./types";

export interface CategoryMeta {
  id: CategoryId;
  name: string;
  tagline: string;
  blurb: string;
}

export const CATEGORIES: CategoryMeta[] = [
  {
    id: "parametric",
    name: "Parametric Statistics",
    tagline: "Local asymptotic normality & efficiency",
    blurb:
      "Differentiability in quadratic mean, the LAN expansion of the log-likelihood, and the Hájek–Le Cam convolution and local asymptotic minimax bounds that pin down efficiency in smooth parametric models.",
  },
  {
    id: "hypothesistesting",
    name: "Hypothesis Tests",
    tagline: "Neyman–Pearson, UMP tests & permutation",
    blurb:
      "The Neyman–Pearson lemma, monotone likelihood ratio and UMP tests, unbiasedness and Neyman structure, invariance and maximal invariants, goodness-of-fit, permutation tests and the bootstrap.",
  },
  {
    id: "pointestimation",
    name: "Point Estimation",
    tagline: "Sufficiency, UMVU & equivariance",
    blurb:
      "Exponential families and sufficiency, completeness and Basu's theorem, the Rao–Blackwell and Lehmann–Scheffé route to UMVU estimators, the Cramér–Rao information inequality, and equivariant estimation.",
  },
  {
    id: "semiparametric",
    name: "Semiparametric Statistics",
    tagline: "Tangent spaces & efficient influence functions",
    blurb:
      "Tangent sets, the efficient influence function as a projection, score and information operators, and the convolution and minimax bounds and efficient estimators of semiparametric theory.",
  },
  {
    id: "concentration",
    name: "Probability Inequalities",
    tagline: "Tail bounds, CLTs & empirical processes",
    blurb:
      "Sub-Gaussian and sub-exponential tails, Hoeffding, Bernstein and McDiarmid, maximal inequalities over covering classes, Berry–Esseen and Lindeberg central limit theorems, and empirical-process limits.",
  },
  {
    id: "highdim",
    name: "High-Dimensional Statistics",
    tagline: "OLS, Lasso rates & compressed sensing",
    blurb:
      "Ordinary least squares mean-squared error, deterministic and random-noise rates for the Lasso, support recovery, compressed-sensing recovery under cone and restricted-isometry conditions, and M-estimators.",
  },
  {
    id: "multipletesting",
    name: "Multiple Testing",
    tagline: "FDR, FWER, knockoffs & goodness-of-fit",
    blurb:
      "Benjamini–Hochberg FDR control, Holm and Bonferroni FWER control, the knockoff filter, e-values and conformal coverage, and goodness-of-fit tests such as Kolmogorov–Smirnov and chi-squared.",
  },
  {
    id: "minimaxity",
    name: "Minimaxity",
    tagline: "Le Cam, Fano & minimax lower bounds",
    blurb:
      "The estimation-to-testing reduction, Le Cam's two-point and convex-hull methods, Fano's inequality with local packing and the Yang–Barron bound, and worked minimax rates for location, regression and PCA.",
  },
  {
    id: "optimization",
    name: "Optimization",
    tagline: "Gradient, proximal & accelerated methods",
    blurb:
      "Convexity and smoothness primitives, co-coercivity, the O(1/t) rates of gradient descent, Frank–Wolfe and proximal gradient, and the O(1/t²) rates of Nesterov-accelerated gradient and proximal methods.",
  },
  {
    id: "bayesian",
    name: "Bayesian Statistics",
    tagline: "Conjugacy, hierarchical models & MCMC",
    blurb:
      "Posterior and predictive densities, sufficiency and conjugate families, Bayes decision theory and the route to minimaxity, MCMC correctness, hierarchical and empirical Bayes, and the Bernstein–von Mises theorem.",
  },
  {
    id: "nonparametric",
    name: "Nonparametric Statistics",
    tagline: "Kernel estimators, projections & RKHS",
    blurb:
      "Kernel density estimation over Hölder classes, local polynomial regression, projection estimators, and reproducing-kernel Hilbert spaces from Moore–Aronszajn to Mercer's theorem and the representer theorem.",
  },
  {
    id: "statisticalmodels",
    name: "Statistical Models",
    tagline: "Survival, mixed effects, GEE & missing data",
    blurb:
      "Statistical models over an abstract parameter space: survival analysis with censoring, Kaplan–Meier and the Cox model, linear mixed effects and BLUP, GEE sandwich covariance, and missing-data mechanisms with IPW.",
  },
  {
    id: "robust",
    name: "Robust Statistics",
    tagline: "Contamination, breakdown & heavy tails",
    blurb:
      "Gross-error contamination, influence functions and breakdown points, Huber M-estimation and the median's minimax bias, scale and regression quantiles, and modern sub-Gaussian mean estimation under heavy tails.",
  },
  {
    id: "probability",
    name: "Miscellaneous Results",
    tagline: "Load-bearing probability & analysis",
    blurb:
      "Standard theorems — Prékopa–Leindler, Anderson's lemma, Le Cam's first and third lemmas, the multivariate CLT, Cramér–Wold, Slutsky, Pólya's theorem and Halmos–Savage — formalized as infrastructure.",
  },
  {
    id: "timeseries",
    name: "Time Series",
    tagline: "Spectra, mixing & nonlinear models",
    blurb:
      "Stationarity and autocovariance, the Herglotz representation and spectral density, linear filters and ARMA, strong-mixing coefficients and their limit theorems, and the ARCH, GARCH and volatility models.",
  },
  {
    id: "causal",
    name: "Causal Inference",
    tagline: "Potential outcomes, IV & double robustness",
    blurb:
      "Potential outcomes and estimands, randomized experiments and Neyman inference, identification by adjustment and matching, augmented inverse-probability weighting and double robustness, and instrumental variables.",
  },
  {
    id: "statlearning",
    name: "Statistical Learning",
    tagline: "PAC learning, VC dimension & kernel methods",
    blurb:
      "Empirical risk minimization and uniform convergence, PAC and agnostic learnability of finite classes, VC dimension and growth functions, Rademacher complexity and symmetrization, stability and PAC-Bayes bounds, and the reproducing-kernel Hilbert spaces behind the representer theorem and the maximal-margin classifier.",
  },
  {
    id: "expdesign",
    name: "Experimental Design",
    tagline: "Randomization, ANOVA & survey sampling",
    blurb:
      "Randomization and sampling designs as distributions over allocations, completely randomized and blocked experiments, the analysis-of-variance identity, factorial characters, and Horvitz-Thompson estimation.",
  },
  {
    id: "compstat",
    name: "Computational Statistics",
    tagline: "Monte Carlo, resampling & simulation correctness",
    blurb:
      "The mathematics that makes simulation-based inference correct: Monte Carlo estimation and its error, importance sampling and the optimal importance density, rejection sampling, Markov chain Monte Carlo, multinomial resampling of particles, the finite-sample bootstrap and jackknife, and cross-validation.",
  },
];

export const CATEGORY_BY_ID: Record<CategoryId, CategoryMeta> = Object.fromEntries(
  CATEGORIES.map((c) => [c.id, c]),
) as Record<CategoryId, CategoryMeta>;
