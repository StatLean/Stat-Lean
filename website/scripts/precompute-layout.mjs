#!/usr/bin/env node
/**
 * Precompute the global dependency-graph layout at build time.
 *
 * Why this exists: `Dependencies.tsx` used to run fcose in the browser on every
 * mount and every filter change. Measured cost was ~2.8 s of blocked main
 * thread for the default view and over ten minutes with Mathlib shown.
 *
 * A previous attempt at build-time layout was reverted because it looked wrong.
 * The cause is recorded in CONTRIBUTING.md: it ran fcose with
 * `randomize: true`, which produces a different arrangement from the browser's.
 * This script instead reproduces the browser recipe exactly —
 *
 *   1. seed every node near the centre, `(rand() - 0.5) * 40`;
 *   2. run fcose with `randomize: false`, same parameters as the page;
 *
 * — with `Math.random` swapped for a seeded PRNG so the result is byte-stable
 * across runs and machines. Same recipe, same shape, computed once.
 *
 * Output: `src/data/layout.json` — `{ seed, count, positions: { [id]: [x, y] } }`
 * with coordinates rounded to one decimal (the drift animation moves nodes far
 * more than that, so the precision is irrelevant and it halves the file).
 *
 * Run via `npm run layout` (and it is wired into `npm run build`).
 */
import { readFileSync, writeFileSync, readdirSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import cytoscape from "cytoscape";
import fcose from "cytoscape-fcose";

cytoscape.use(fcose);

const HERE = dirname(fileURLToPath(import.meta.url));
const DATA = join(HERE, "..", "src", "data");
const GRAPHS = join(DATA, "graphs");
const OUT = join(DATA, "layout.json");

const SEED = 20260810;

/** mulberry32 — small, fast, deterministic. */
function mulberry32(a) {
  return function () {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---- union the per-result graphs (mirrors src/lib/globalGraph.ts) ----
const nodes = new Map();
const edgeSet = new Set();
for (const f of readdirSync(GRAPHS)) {
  if (!f.endsWith(".json")) continue;
  const g = JSON.parse(readFileSync(join(GRAPHS, f), "utf8"));
  for (const n of g.nodes) {
    const norm = { ...n, kind: n.kind === "root" ? "repo" : n.kind };
    const existing = nodes.get(n.id);
    if (!existing) nodes.set(n.id, norm);
    else if (existing.kind === "mathlib" && norm.kind === "repo")
      existing.kind = "repo";
  }
  for (const e of g.edges) edgeSet.add(e.source + " " + e.target);
}
const edges = [...edgeSet]
  .map((s) => {
    const [source, target] = s.split(" ");
    return { source, target };
  })
  .filter((e) => nodes.has(e.source) && nodes.has(e.target));

console.log(`[layout] ${nodes.size} nodes, ${edges.length} edges`);

// ---- deterministic run: seed the PRNG, then reproduce the page's recipe ----
const rand = mulberry32(SEED);
const realRandom = Math.random;
Math.random = rand;

const cy = cytoscape({
  headless: true,
  styleEnabled: false,
  elements: {
    nodes: [...nodes.values()].map((n) => ({ data: { id: n.id } })),
    edges: edges.map((e, i) => ({
      data: { id: "e" + i, source: e.source, target: e.target },
    })),
  },
});

// 1. seed at the centre, exactly as the page does before its layout
cy.nodes().positions(() => ({
  x: (Math.random() - 0.5) * 40,
  y: (Math.random() - 0.5) * 40,
}));

// 2. the page's fcose parameters, minus the animation
const t0 = Date.now();
cy.layout({
  name: "fcose",
  quality: "default",
  animate: false,
  randomize: false, // start from the central cluster → explode outward
  fit: true,
  padding: 50,
  packComponents: false,
  nodeSeparation: 60,
  idealEdgeLength: 42,
  nodeRepulsion: 7000,
  gravity: 0.4,
  gravityRange: 3,
  numIter: 600,
}).run();
console.log(`[layout] fcose finished in ${((Date.now() - t0) / 1000).toFixed(1)}s`);

Math.random = realRandom;

const positions = {};
cy.nodes().forEach((n) => {
  const p = n.position();
  positions[n.id()] = [Math.round(p.x * 10) / 10, Math.round(p.y * 10) / 10];
});

writeFileSync(
  OUT,
  JSON.stringify({ seed: SEED, count: cy.nodes().length, positions }) + "\n",
);
console.log(`[layout] wrote ${OUT} (${cy.nodes().length} positions)`);
