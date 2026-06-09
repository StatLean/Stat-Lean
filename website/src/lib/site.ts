import type { ResultEntry } from "./types";

export const REPO_URL =
  "https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory";

export const DOCS_BASE =
  "https://junwei-lu.github.io/Lean-Asymptotic-Statistical-Theory/docs/";

/** Absolute doc-gen4 URL for a result (robust in dev and prod). */
export function docUrl(r: ResultEntry): string {
  // stored as "../docs/AsymptoticStatistics/<path>.html#<fullName>"
  const tail = r.docGenUrl.replace(/^(\.\.\/)?docs\//, "");
  return DOCS_BASE + tail;
}

/** GitHub source link for a result's file. */
export function sourceUrl(r: ResultEntry): string {
  return `${REPO_URL}/blob/main/${r.file}`;
}

/**
 * doc-gen4 URL for any declaration, keyed by its *defining module* (not its
 * namespace). The project's doc-gen4 site hosts both repo and Mathlib pages, so
 * this resolves for every node. Example:
 *   module "Mathlib.Analysis.InnerProductSpace.Projection.Basic",
 *   full   "Submodule.sub_starProjection_mem_orthogonal"
 *   → …/docs/Mathlib/Analysis/InnerProductSpace/Projection/Basic.html#Submodule.sub_starProjection_mem_orthogonal
 */
export function docUrlForNode(module: string, full: string): string {
  return DOCS_BASE + module.split(".").join("/") + ".html#" + full;
}
