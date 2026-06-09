import type { CategoryId, DepNode } from "./types";
import { RESULTS } from "./data";

export type Area = CategoryId | "external";

/** CSS custom property holding each area's RGB triplet. */
export const AREA_VAR: Record<Area, string> = {
  parametric: "--c-param",
  semiparametric: "--c-semi",
  empirical: "--c-emp",
  probability: "--c-prob",
  external: "--c-ext",
};

export const AREA_LABEL: Record<Area, string> = {
  parametric: "Parametric",
  semiparametric: "Semiparametric",
  empirical: "Empirical Processes",
  probability: "Probability",
  external: "Mathlib / external",
};

/** Top-level source folder of a result file, e.g.
 *  "AsymptoticStatistics/Core/EIF.lean" → "Core". */
function folderOfFile(file: string): string {
  return file.split("/")[1] ?? "";
}

/** Top-level source folder from a defining module, e.g.
 *  "AsymptoticStatistics.Core.EIF" → "Core". */
function folderOfModule(module: string): string {
  return module.split(".")[1] ?? "";
}

/** fullName → its category, for the user-facing results. */
const USER_FACING: Map<string, CategoryId> = new Map(
  RESULTS.map((r) => [r.fullName, r.category]),
);

/**
 * Folder → category, derived from the data: each folder takes the category that
 * the majority of its user-facing results belong to (argmax). No hand-authored
 * table — `Core`, `ForMathlib`, etc. resolve from `results.json`.
 */
const FOLDER_CATEGORY: Map<string, CategoryId> = (() => {
  const tally = new Map<string, Map<CategoryId, number>>();
  for (const r of RESULTS) {
    const folder = folderOfFile(r.file);
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
  if (node.kind === "mathlib" || !node.module.startsWith("AsymptoticStatistics"))
    return "external";
  return FOLDER_CATEGORY.get(folderOfModule(node.module)) ?? rootArea;
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
