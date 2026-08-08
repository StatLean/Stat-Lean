// Chapter (or lecture) titles for the main textbooks, used to render the
// reference-page dropdowns as a chapter-ordered table of contents. Titles are
// authored from each book's table of contents; a chapter absent from the map
// falls back to a bare "Chapter N".

/** Reference keys that get a chapter-ordered TOC (vs. a flat citing-results list). */
export const TEXTBOOK_KEYS = new Set([
  "vdv1998",
  "lu-bda",
  "wainwright2019",
  "candes-stat300c",
  "vershynin2018",
  "robert2007",
  "gelman2014",
  "tsybakov2009",
  "lehmann-romano2022",
  "lehmann-casella1998",
]);

export function isTextbook(key: string): boolean {
  return TEXTBOOK_KEYS.has(key);
}

/** The unit word for a book's top-level division ("Chapter" by default). */
const CHAPTER_WORD: Record<string, string> = {
  "candes-stat300c": "Lecture",
};

export function chapterWord(key: string): string {
  return CHAPTER_WORD[key] ?? "Chapter";
}

const CHAPTER_TITLES: Record<string, Record<number, string>> = {
  vdv1998: {
    2: "Stochastic Convergence",
    3: "Delta Method",
    4: "Moment Estimators",
    5: "M- and Z-Estimators",
    6: "Contiguity",
    7: "Local Asymptotic Normality",
    8: "Efficiency of Estimators",
    18: "Stochastic Convergence in Metric Spaces",
    19: "Empirical Processes",
    25: "Semiparametric Models",
  },
  "lehmann-romano2022": {
    3: "Uniformly Most Powerful Tests",
    4: "Unbiasedness: Theory and First Applications",
    6: "Invariance",
    11: "Basic Large-Sample Theory",
    12: "Extensions of the CLT to Sums of Dependent Random Variables",
    14: "Quadratic Mean Differentiable Families",
    16: "Testing Goodness of Fit",
    17: "Permutation and Randomization Tests",
    18: "Bootstrap and Subsampling Methods",
  },
  "lehmann-casella1998": {
    1: "Preparations",
    2: "Unbiasedness",
    3: "Equivariance",
  },
  "lu-bda": {
    4: "Sub-Gaussian Random Variables",
    5: "Sub-Exponential Random Variables",
    6: "Bernstein and Maximal Inequalities",
    7: "Ordinary Least Squares",
    8: "Compressed Sensing",
    9: "Restricted Isometry and Recovery",
    10: "The Lasso",
    12: "Convex Optimization",
    13: "Gradient Descent",
    14: "Proximal and Accelerated Methods",
    19: "Family-Wise Error Rate",
    20: "False Discovery Rate",
    21: "Knockoffs",
  },
  wainwright2019: {
    2: "Basic Tail and Concentration Bounds",
    4: "Uniform Laws of Large Numbers",
    5: "Metric Entropy and Its Uses",
    6: "Random Matrices and Covariance Estimation",
    7: "Sparse Linear Models in High Dimensions",
    9: "Decomposability and Restricted Strong Convexity",
    10: "Matrix Estimation with Rank Constraints",
    15: "Minimax Lower Bounds",
  },
  "candes-stat300c": {
    2: "Chi-Squared Goodness-of-Fit",
    3: "Kolmogorov–Smirnov Test",
    5: "False Discovery Rate",
    7: "Benjamini–Hochberg Procedure",
    9: "Order Statistics and Ranks",
    15: "E-values and Empirical Bayes",
    19: "Conformal Inference",
    20: "False Discovery Rate",
    21: "Knockoffs",
  },
  vershynin2018: {
    2: "Concentration of Sums of Independent Random Variables",
    3: "Random Vectors in High Dimensions",
    6: "Quadratic Forms, Symmetrization and Contraction",
    8: "Chaining",
  },
  robert2007: {
    1: "Introduction",
    2: "Decision-Theoretic Foundations",
    3: "From Prior Information to Prior Distributions",
    4: "Bayesian Point Estimation",
    5: "Tests and Confidence Regions",
    6: "Bayesian Calculations",
    7: "Model Choice",
    10: "Hierarchical and Empirical Bayes Extensions",
  },
  tsybakov2009: {
    1: "Nonparametric Estimators",
    2: "Lower Bounds on the Minimax Risk",
    3: "Asymptotic Efficiency and Adaptation",
  },
  gelman2014: {
    1: "Probability and Inference",
    2: "Single-Parameter Models",
    3: "Introduction to Multiparameter Models",
    5: "Hierarchical Models",
    11: "Basics of Markov Chain Simulation",
  },
};

export function chapterTitle(key: string, ch: number): string | undefined {
  return CHAPTER_TITLES[key]?.[ch];
}
