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
    id: "semiparametric",
    name: "Semiparametric Statistics",
    tagline: "Tangent spaces & efficient influence functions",
    blurb:
      "Tangent sets, the efficient influence function as a projection, score and information operators, and the convolution / minimax bounds and efficient estimators of semiparametric theory.",
  },
  {
    id: "concentration",
    name: "Concentration Inequalities",
    tagline: "Sub-Gaussian tails, Bernstein & empirical processes",
    blurb:
      "Sub-Gaussian and sub-exponential tail bounds, Hoeffding, Bernstein and McDiarmid inequalities, maximal inequalities over finite and covering classes, and the empirical-process limits (Glivenko–Cantelli, Donsker) that build on them.",
  },
  {
    id: "highdim",
    name: "High-Dimensional Statistics",
    tagline: "OLS, Lasso rates & compressed sensing",
    blurb:
      "Ordinary least squares mean-squared error, deterministic and random-noise ℓ²-rates for the Lasso, support-recovery guarantees, compressed-sensing recovery under the cone and restricted-isometry conditions, and M-estimator deviation bounds.",
  },
  {
    id: "multipletesting",
    name: "Multiple Testing",
    tagline: "FDR, FWER, knockoffs & goodness-of-fit",
    blurb:
      "Benjamini–Hochberg FDR control, Holm and Bonferroni FWER control, the knockoff filter, e-values and conformal coverage, and goodness-of-fit tests including Kolmogorov–Smirnov and the chi-squared statistic.",
  },
  {
    id: "minimaxity",
    name: "Minimaxity",
    tagline: "Le Cam, Fano & minimax lower bounds",
    blurb:
      "The estimation-to-testing reduction, Le Cam's two-point and convex-hull methods, Fano's inequality with local packing and the Yang–Barron bound, and worked minimax rates for location, regression, PCA and density estimation.",
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
      "The dominated-Bayes posterior and predictive densities, sufficiency and conjugate families (Beta–Binomial, Gamma–Poisson, Normal–Normal, Dirichlet–Multinomial), Bayes decision theory and the route to minimaxity, model choice and MCMC correctness, and the hierarchical + empirical-Bayes theory — posterior tower/mixture, partial pooling, James–Stein, Tweedie, and the NPMLE.",
  },
  {
    id: "probability",
    name: "Miscellaneous Results",
    tagline: "Load-bearing probability & analysis",
    blurb:
      "Standard theorems — Prékopa–Leindler, Anderson's lemma, Le Cam's first and third lemmas, the multivariate CLT, Cramér–Wold, Slutsky, and Doob L² isometries — formalized as infrastructure.",
  },
];

export const CATEGORY_BY_ID: Record<CategoryId, CategoryMeta> = Object.fromEntries(
  CATEGORIES.map((c) => [c.id, c]),
) as Record<CategoryId, CategoryMeta>;
