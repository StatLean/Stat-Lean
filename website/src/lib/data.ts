import type { CategoryId, DepGraph, ResultEntry } from "./types";
import rawResults from "../data/results.json";

export const RESULTS = rawResults as unknown as ResultEntry[];

export function resultsByCategory(cat: CategoryId): ResultEntry[] {
  return RESULTS.filter((r) => r.category === cat);
}

export function getResult(id: string): ResultEntry | undefined {
  return RESULTS.find((r) => r.id === id);
}

export function countByCategory(cat: CategoryId): number {
  return RESULTS.reduce((n, r) => (r.category === cat ? n + 1 : n), 0);
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
