import type { CategoryId, DepGraph, ResultEntry } from "./types";
import rawResults from "../data/results.json";

export const RESULTS = rawResults as unknown as ResultEntry[];

/** Is this result listed under `cat` — as its own topic or by cross-listing? */
export function inCategory(r: ResultEntry, cat: CategoryId): boolean {
  return r.category === cat || (r.crossListed?.includes(cat) ?? false);
}

/**
 * The results listed under `cat`: the topic's own results first, in file order,
 * then the ones cross-listed into it. A topic should lead with the results it is
 * about — cross-listed pages are related material, not its headline content.
 */
export function resultsByCategory(cat: CategoryId): ResultEntry[] {
  const own = RESULTS.filter((r) => r.category === cat);
  const borrowed = RESULTS.filter((r) => r.category !== cat && inCategory(r, cat));
  return [...own, ...borrowed];
}

export function getResult(id: string): ResultEntry | undefined {
  return RESULTS.find((r) => r.id === id);
}

export function countByCategory(cat: CategoryId): number {
  return RESULTS.reduce((n, r) => (inCategory(r, cat) ? n + 1 : n), 0);
}

// Lazy-load generated dependency graphs (one JSON per result id).
const graphModules = import.meta.glob<{ default: DepGraph }>(
  "../data/graphs/*.json",
);

export async function loadGraph(id: string): Promise<DepGraph | null> {
  const key = `../data/graphs/${id}.json`;
  const loader = graphModules[key];
  if (!loader) return null;
  try {
    const mod = await loader();
    return mod.default;
  } catch {
    return null;
  }
}
