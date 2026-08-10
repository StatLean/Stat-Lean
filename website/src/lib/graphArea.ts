import type { CategoryId, DepNode } from "./types";
import { RESULTS } from "./data";

export type Area = CategoryId | "external";

/** CSS custom property holding each area's RGB triplet. */
export const AREA_VAR: Record<Area, string> = {
  parametric: "--c-param",
  semiparametric: "--c-semi",
  concentration: "--c-conc",
  highdim: "--c-highdim",
  multipletesting: "--c-hyp",
  minimaxity: "--c-mmx",
  optimization: "--c-opt",
  bayesian: "--c-bayes",
  nonparametric: "--c-nonparam",
  statisticalmodels: "--c-smod",
  probability: "--c-prob",
  hypothesistesting: "--c-htest",
  pointestimation: "--c-pest",
  timeseries: "--c-ts",
  causal: "--c-causal",
  statlearning: "--c-slearn",
  expdesign: "--c-exp",
  external: "--c-ext",
};

export const AREA_LABEL: Record<Area, string> = {
  parametric: "Parametric",
  semiparametric: "Semiparametric",
  concentration: "Concentration",
  highdim: "High-Dimensional",
  multipletesting: "Multiple Testing",
  minimaxity: "Minimaxity",
  optimization: "Optimization",
  bayesian: "Bayesian",
  nonparametric: "Nonparametric",
  statisticalmodels: "Statistical Models",
  probability: "Miscellaneous",
  hypothesistesting: "Hypothesis Tests",
  pointestimation: "Point Estimation",
  timeseries: "Time Series",
  causal: "Causal Inference",
  statlearning: "Statistical Learning",
  expdesign: "Experimental Design",
  external: "Mathlib / external",
};

/** Ordered list of areas for legends / swatch rows. */
export const AREAS: Area[] = [
  "parametric",
  "semiparametric",
  "concentration",
  "highdim",
  "multipletesting",
  "minimaxity",
  "optimization",
  "bayesian",
  "nonparametric",
  "statisticalmodels",
  "probability",
  "hypothesistesting",
  "pointestimation",
  "timeseries",
  "causal",
  "statlearning",
  "expdesign",
  "external",
];

/**
 * Top-level Lean area directory (the segment under `StatLean/`) → category, for
 * the areas that map one-to-one. AsymptoticStatistics is finer-grained than its
 * directory (it splits into parametric / semiparametric / concentration /
 * probability) and is resolved by the per-subfolder vote below instead.
 */
const DIR_AREA: Partial<Record<string, CategoryId>> = {
  Bayesian: "bayesian",
  NonparametricStatistics: "nonparametric",
  StatisticalModels: "statisticalmodels",
  ConcentrationInequalities: "concentration",
  HighDimensionalStatistics: "highdim",
  MultipleTesting: "multipletesting",
  Minimaxity: "minimaxity",
  Optimization: "optimization",
  HypothesisTesting: "hypothesistesting",
  PointEstimation: "pointestimation",
  TimeSeries: "timeseries",
  CausalInference: "causal",
  StatisticalLearning: "statlearning",
  ExperimentalDesign: "expdesign",
};

/** Drop an optional leading `StatLean.` / `StatLean/` root segment. */
function stripRoot(path: string, sep: "." | "/"): string {
  const prefix = "StatLean" + sep;
  return path.startsWith(prefix) ? path.slice(prefix.length) : path;
}

/** Area directory of a result file, e.g.
 *  "StatLean/AsymptoticStatistics/Core/EIF.lean" → "AsymptoticStatistics". */
function areaDirOfFile(file: string): string {
  return stripRoot(file, "/").split("/")[0] ?? "";
}

/** AsymptoticStatistics subfolder of a file, e.g.
 *  "StatLean/AsymptoticStatistics/Core/EIF.lean" → "Core". */
function subfolderOfFile(file: string): string {
  return stripRoot(file, "/").split("/")[1] ?? "";
}

/** Area directory of a defining module, e.g.
 *  "StatLean.AsymptoticStatistics.Core.EIF" → "AsymptoticStatistics". */
function areaDirOfModule(module: string): string {
  return stripRoot(module, ".").split(".")[0] ?? "";
}

/** AsymptoticStatistics subfolder of a module, e.g.
 *  "StatLean.AsymptoticStatistics.Core.EIF" → "Core". */
function subfolderOfModule(module: string): string {
  return stripRoot(module, ".").split(".")[1] ?? "";
}

/** fullName → its category, for the user-facing results. */
const USER_FACING: Map<string, CategoryId> = new Map(
  RESULTS.map((r) => [r.fullName, r.category]),
);

/**
 * AsymptoticStatistics subfolder → category, derived from the data: each
 * subfolder takes the category that the majority of its user-facing results
 * belong to (argmax). No hand-authored table — `Core`, `ForMathlib`,
 * `EmpiricalProcess`, etc. resolve from `results.json`. Only AsymptoticStatistics
 * needs this; the other areas map one-to-one through `DIR_AREA`.
 */
const FOLDER_CATEGORY: Map<string, CategoryId> = (() => {
  const tally = new Map<string, Map<CategoryId, number>>();
  for (const r of RESULTS) {
    if (areaDirOfFile(r.file) !== "AsymptoticStatistics") continue;
    const folder = subfolderOfFile(r.file);
    if (!folder) continue;
    const counts = tally.get(folder) ?? new Map<CategoryId, number>();
    counts.set(r.category, (counts.get(r.category) ?? 0) + 1);
    tally.set(folder, counts);
  }
  const out = new Map<string, CategoryId>();
  for (const [folder, counts] of tally) {
    let best: CategoryId | null = null;
    let bestN = -1;
    for (const [cat, n] of counts) {
      if (n > bestN) {
        bestN = n;
        best = cat;
      }
    }
    if (best) out.set(folder, best);
  }
  return out;
})();

export function isUserFacing(full: string): boolean {
  return USER_FACING.has(full);
}

/** Resolve a node's area for coloring (home-area mapping). */
export function nodeArea(node: DepNode, rootArea: CategoryId): Area {
  const own = USER_FACING.get(node.full);
  if (own) return own;
  if (node.kind === "mathlib") return "external";
  const dir = areaDirOfModule(node.module);
  const mapped = DIR_AREA[dir];
  if (mapped) return mapped;
  if (dir === "AsymptoticStatistics")
    return FOLDER_CATEGORY.get(subfolderOfModule(node.module)) ?? rootArea;
  // Unknown / core-Lean module that wasn't flagged as mathlib → treat as external.
  return "external";
}

/**
 * Cytoscape node shape:
 *  - definition / structure  → round   (round-rectangle)
 *  - user-facing theorem     → square  (rectangle)
 *  - auxiliary lemma/result  → ellipse
 */
export function nodeShape(node: DepNode): "rectangle" | "ellipse" | "round-rectangle" {
  if (node.decl === "def") return "round-rectangle";
  return isUserFacing(node.full) ? "rectangle" : "ellipse";
}
