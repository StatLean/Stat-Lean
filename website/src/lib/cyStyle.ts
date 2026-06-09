import { nodeArea, nodeShape, AREA_VAR, type Area } from "./graphArea";
import type { CategoryId, DepNode } from "./types";

/** Raw "r g b" triplet behind a CSS custom property. */
export function triplet(name: string): string {
  const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  return v || "136 136 136";
}
// Cytoscape needs comma-separated rgb()/rgba(), not the CSS-4 space syntax.
const csv = (t: string) => t.trim().split(/\s+/).join(",");
export const rgb = (t: string) => `rgb(${csv(t)})`;
export const rgba = (t: string, a: number) => `rgba(${csv(t)},${a})`;
function lum(t: string): number {
  const [r, g, b] = t.split(/\s+/).map(Number);
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}
const contrastTriplet = (t: string) => (lum(t) > 145 ? "26 24 20" : "247 243 235");

export function areaTriplets(): Record<Area, string> {
  return {
    parametric: triplet(AREA_VAR.parametric),
    semiparametric: triplet(AREA_VAR.semiparametric),
    empirical: triplet(AREA_VAR.empirical),
    probability: triplet(AREA_VAR.probability),
    external: triplet(AREA_VAR.external),
  };
}

/**
 * Cytoscape node `data` for a dependency node — shared by the per-result graph
 * and the global Dependencies graph so they look identical. Color = area,
 * shape = declaration role; `emphasize` (a result's root, or a user-facing node
 * in the global graph) gets a thick ink ring.
 */
export function buildNodeData(
  n: DepNode,
  opts: { rootArea: CategoryId; emphasize: boolean; ats: Record<Area, string> },
) {
  const area = nodeArea(n, opts.rootArea);
  const at = opts.ats[area];
  const ink = triplet("--ink");
  return {
    id: n.id,
    label: n.label,
    full: n.full,
    module: n.module,
    area,
    shape: nodeShape(n),
    fill: rgb(at),
    border: opts.emphasize ? rgb(ink) : rgba(at, 0.55),
    borderWidth: opts.emphasize ? 3 : 1,
    labelColor: rgb(contrastTriplet(at)),
    fontWeight: opts.emphasize ? 600 : 400,
  };
}

/** Shared node + edge stylesheet. */
export function styleSheet(): any[] {
  const rule = triplet("--rule");
  return [
    {
      selector: "node",
      style: {
        label: "data(label)",
        "font-family": "JetBrains Mono, monospace",
        "font-size": 11,
        "font-weight": "data(fontWeight)",
        color: "data(labelColor)",
        "text-valign": "center",
        "text-halign": "center",
        "text-max-width": "210px",
        shape: "data(shape)",
        width: "label",
        height: "label",
        padding: "9px",
        "background-color": "data(fill)",
        "border-width": "data(borderWidth)",
        "border-color": "data(border)",
        "border-style": "solid",
      },
    },
    {
      selector: "edge",
      style: {
        width: 1.4,
        "line-color": rgb(rule),
        "target-arrow-color": rgb(rule),
        "target-arrow-shape": "triangle",
        "arrow-scale": 0.8,
        "curve-style": "bezier",
        opacity: 0.8,
      },
    },
    { selector: ".faded", style: { opacity: 0.12 } },
  ];
}
