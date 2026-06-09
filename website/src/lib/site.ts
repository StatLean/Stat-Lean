import type { ResultEntry } from "./types";

export const REPO_URL =
  "https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory";

export const DOCS_BASE =
  "https://junwei-lu.github.io/Lean-Asymptotic-Statistical-Theory/docs/";

const MATHLIB_DOCS_BASE = "https://leanprover-community.github.io/mathlib4_docs/";

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
 * doc-gen4 URL for any declaration, keyed by its defining module.
 * Mathlib and Batteries declarations are hosted at leanprover-community.github.io;
 * project declarations are hosted at the project's own doc-gen4 site.
 */
export function docUrlForNode(module: string, full: string): string {
  const base =
    module.startsWith("Mathlib") || module.startsWith("Batteries")
      ? MATHLIB_DOCS_BASE
      : DOCS_BASE;
  return base + module.split(".").join("/") + ".html#" + full;
}
