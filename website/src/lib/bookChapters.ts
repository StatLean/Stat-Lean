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
    5: "M- and Z-Estimators",
    6: "Contiguity",
    7: "Local Asymptotic Normality",
    8: "Efficiency of Estimators",
    18: "Stochastic Convergence in Metric Spaces",
    19: "Empirical Processes",
    25: "Semiparametric Models",
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
};

export function chapterTitle(key: string, ch: number): string | undefined {
  return CHAPTER_TITLES[key]?.[ch];
}
