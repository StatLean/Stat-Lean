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
    id: "empirical",
    name: "Empirical Processes",
    tagline: "Glivenko–Cantelli, Donsker & maximal inequalities",
    blurb:
      "Bracketing entropy conditions yielding the Glivenko–Cantelli and Donsker properties, maximal inequalities, and empirical-process limits under estimated parameters.",
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
