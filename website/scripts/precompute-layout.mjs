#!/usr/bin/env node
/**
 * Build compact global dependency-graph assets and an offline force layout.
 *
 * The browser used to import and union every per-result graph (7.8 MB) and run
 * fcose on the main thread.  This script performs both jobs once.  The initial
 * asset contains only StatLean nodes; Mathlib nodes and their edges are stored
 * separately and fetched only when the visitor asks for them.
 */
import { readFileSync, writeFileSync, readdirSync, existsSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import cytoscape from "cytoscape";
import fcose from "cytoscape-fcose";

cytoscape.use(fcose);

const HERE = dirname(fileURLToPath(import.meta.url));
const DATA = join(HERE, "..", "src", "data");
const GRAPHS = join(DATA, "graphs");
const ALL_RESULTS = JSON.parse(readFileSync(join(DATA, "results.json"), "utf8"));
// Hidden results have no page on the site, so they contribute no node here
// either — their graph file is skipped in the union below.
const RESULTS = ALL_RESULTS.filter((r) => !r.hidden);
const HIDDEN_GRAPHS = new Set(
  ALL_RESULTS.filter((r) => r.hidden).map((r) => `${r.id}.json`),
);
const CORE_GRAPH = join(DATA, "global-core.json");
const EXTERNAL_GRAPH = join(DATA, "global-external.json");
const CORE_LAYOUT = join(DATA, "layout-core.json");
const FULL_LAYOUT = join(DATA, "layout-full.json");
const LEGACY_LAYOUT = join(DATA, "layout.json");
const SEED = 20260811;
const GAP = 5;

function mulberry32(a) {
  return function () {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const userFacing = new Map(RESULTS.map((r) => [r.fullName, r.category]));
const dirArea = {
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

const folderVotes = new Map();
for (const r of RESULTS) {
  const parts = r.file.replace(/^StatLean\//, "").split("/");
  if (parts[0] !== "AsymptoticStatistics" || !parts[1]) continue;
  const votes = folderVotes.get(parts[1]) ?? new Map();
  votes.set(r.category, (votes.get(r.category) ?? 0) + 1);
  folderVotes.set(parts[1], votes);
}
const folderArea = new Map();
for (const [folder, votes] of folderVotes) {
  folderArea.set(folder, [...votes].sort((a, b) => b[1] - a[1])[0][0]);
}

function areaOf(node) {
  const own = userFacing.get(node.full);
  if (own) return own;
  if (node.kind === "mathlib") return "external";
  const parts = node.module.replace(/^StatLean\./, "").split(".");
  if (dirArea[parts[0]]) return dirArea[parts[0]];
  if (parts[0] === "AsymptoticStatistics") return folderArea.get(parts[1]) ?? "semiparametric";
  return "external";
}

function nodeSize(node) {
  if (userFacing.has(node.full)) return 19;
  return node.area === "external" ? 7 : 10;
}

// Union the per-result graphs once, preferring a repository classification
// when a declaration appears as both a root and a dependency.
const nodeMap = new Map();
const edgeSet = new Set();
for (const file of readdirSync(GRAPHS).sort()) {
  if (!file.endsWith(".json") || HIDDEN_GRAPHS.has(file)) continue;
  const graph = JSON.parse(readFileSync(join(GRAPHS, file), "utf8"));
  for (const node of graph.nodes) {
    const normalized = { ...node, kind: node.kind === "root" ? "repo" : node.kind };
    const existing = nodeMap.get(node.id);
    if (!existing) nodeMap.set(node.id, normalized);
    else if (existing.kind === "mathlib" && normalized.kind === "repo") existing.kind = "repo";
  }
  for (const edge of graph.edges) edgeSet.add(`${edge.source}\0${edge.target}`);
}

const nodes = [...nodeMap.values()].map((node) => ({ ...node, area: areaOf(node) }));
const nodeById = new Map(nodes.map((node) => [node.id, node]));
const edges = [...edgeSet].flatMap((key) => {
  const [source, target] = key.split("\0");
  return nodeById.has(source) && nodeById.has(target) ? [{ source, target }] : [];
});
const coreNodes = nodes.filter((node) => node.area !== "external");
const externalNodes = nodes.filter((node) => node.area === "external");
const externalIds = new Set(externalNodes.map((node) => node.id));
const coreEdges = edges.filter((edge) => !externalIds.has(edge.source) && !externalIds.has(edge.target));
const externalEdges = edges.filter((edge) => externalIds.has(edge.source) || externalIds.has(edge.target));

writeFileSync(CORE_GRAPH, JSON.stringify({ nodes: coreNodes, edges: coreEdges }) + "\n");
writeFileSync(EXTERNAL_GRAPH, JSON.stringify({ nodes: externalNodes, edges: externalEdges }) + "\n");
console.log(
  `[graph] core ${coreNodes.length} nodes/${coreEdges.length} edges; ` +
    `deferred ${externalNodes.length} nodes/${externalEdges.length} edges`,
);

function fallbackPosition(id) {
  let h = 2166136261;
  for (let i = 0; i < id.length; i += 1) {
    h ^= id.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  const angle = ((h >>> 0) % 3600) / 3600 * Math.PI * 2;
  const radius = 500 + ((h >>> 8) % 1300);
  return [Math.cos(angle) * radius, Math.sin(angle) * radius];
}

/** Resolve axis-aligned collisions without changing the overall force shape. */
function separate(nodesForLayout, positions) {
  const sizes = new Map(nodesForLayout.map((node) => [node.id, nodeSize(node)]));
  const ids = nodesForLayout.map((node) => node.id).sort();
  for (const id of ids) positions[id] ??= fallbackPosition(id);

  const pairs = () => {
    const cellSize = 32;
    const cells = new Map();
    for (const id of ids) {
      const [x, y] = positions[id];
      const key = `${Math.floor(x / cellSize)},${Math.floor(y / cellSize)}`;
      const bucket = cells.get(key) ?? [];
      bucket.push(id);
      cells.set(key, bucket);
    }
    const out = [];
    const seen = new Set();
    for (const id of ids) {
      const [x, y] = positions[id];
      const cx = Math.floor(x / cellSize);
      const cy = Math.floor(y / cellSize);
      for (let dx = -1; dx <= 1; dx += 1) for (let dy = -1; dy <= 1; dy += 1) {
        for (const other of cells.get(`${cx + dx},${cy + dy}`) ?? []) {
          if (id === other) continue;
          const key = id < other ? `${id}\0${other}` : `${other}\0${id}`;
          if (!seen.has(key)) {
            seen.add(key);
            out.push(id < other ? [id, other] : [other, id]);
          }
        }
      }
    }
    return out;
  };

  for (let iteration = 0; iteration < 120; iteration += 1) {
    let overlaps = 0;
    for (const [a, b] of pairs()) {
      const pa = positions[a];
      const pb = positions[b];
      const need = (sizes.get(a) + sizes.get(b)) / 2 + GAP;
      const dx = pb[0] - pa[0];
      const dy = pb[1] - pa[1];
      const ox = need - Math.abs(dx);
      const oy = need - Math.abs(dy);
      if (ox <= 0 || oy <= 0) continue;
      overlaps += 1;
      if (ox < oy) {
        const direction = dx === 0 ? (a < b ? 1 : -1) : Math.sign(dx);
        const move = ox / 2 + 0.25;
        pa[0] -= direction * move;
        pb[0] += direction * move;
      } else {
        const direction = dy === 0 ? (a < b ? 1 : -1) : Math.sign(dy);
        const move = oy / 2 + 0.25;
        pa[1] -= direction * move;
        pb[1] += direction * move;
      }
    }
    if (overlaps === 0) return;
    if (iteration === 119) throw new Error(`[layout] ${overlaps} overlaps remain`);
  }
}

// Recreate the older force-directed arrangement for all current StatLean
// results, but do the expensive work here instead of in the visitor's tab.
const rand = mulberry32(SEED);
const realRandom = Math.random;
Math.random = rand;
const cy = cytoscape({
  headless: true,
  styleEnabled: false,
  elements: {
    nodes: coreNodes.map((node) => ({ data: { id: node.id } })),
    edges: coreEdges.map((edge, index) => ({ data: { id: `e${index}`, ...edge } })),
  },
});
cy.nodes().positions(() => ({ x: (Math.random() - 0.5) * 40, y: (Math.random() - 0.5) * 40 }));
const started = Date.now();
cy.layout({
  name: "fcose",
  quality: "default",
  animate: false,
  randomize: false,
  fit: true,
  padding: 50,
  packComponents: false,
  nodeSeparation: 60,
  idealEdgeLength: 42,
  nodeRepulsion: 7000,
  gravity: 0.4,
  gravityRange: 3,
  numIter: 750,
}).run();
Math.random = realRandom;

const corePositions = {};
cy.nodes().forEach((node) => {
  const p = node.position();
  corePositions[node.id()] = [p.x, p.y];
});
cy.destroy();
const coreValues = Object.values(corePositions);
const coreCentre = coreValues.reduce(
  (sum, position) => [sum[0] + position[0] / coreValues.length, sum[1] + position[1] / coreValues.length],
  [0, 0],
);
for (const id in corePositions) {
  const [x, y] = corePositions[id];
  corePositions[id] = [
    coreCentre[0] + (x - coreCentre[0]) * 4,
    coreCentre[1] + (y - coreCentre[1]) * 4,
  ];
}
for (const id in corePositions) {
  corePositions[id] = corePositions[id].map((value) => Math.round(value * 10) / 10);
}
separate(coreNodes, corePositions);
for (const id in corePositions) {
  corePositions[id] = corePositions[id].map((value) => Math.round(value * 100) / 100);
}
writeFileSync(
  CORE_LAYOUT,
  JSON.stringify({ seed: SEED, count: coreNodes.length, edges: coreEdges.length, minGap: GAP, positions: corePositions }) + "\n",
);
console.log(`[layout] core fcose finished in ${((Date.now() - started) / 1000).toFixed(1)}s`);

// The previous full-graph force layout already includes all current results.
// Keep its large-scale shape, repair any node collisions, and publish it as the
// on-demand Mathlib layout.
const previousPath = existsSync(LEGACY_LAYOUT) ? LEGACY_LAYOUT : FULL_LAYOUT;
const previous = JSON.parse(readFileSync(previousPath, "utf8"));
const fullPositions = { ...previous.positions };
// The legacy full layout treated nodes as points.  Expanding it preserves its
// force-directed silhouette while giving the rendered glyphs room to breathe;
// the collision pass below handles the few coincident coordinates that remain.
const fullValues = Object.values(fullPositions);
const centre = fullValues.reduce(
  (sum, position) => [sum[0] + position[0] / fullValues.length, sum[1] + position[1] / fullValues.length],
  [0, 0],
);
for (const id in fullPositions) {
  const [x, y] = fullPositions[id];
  fullPositions[id] = [centre[0] + (x - centre[0]) * 4, centre[1] + (y - centre[1]) * 4];
}
for (const id in fullPositions) {
  fullPositions[id] = fullPositions[id].map((value) => Math.round(value * 10) / 10);
}
separate(nodes, fullPositions);
for (const id in fullPositions) {
  fullPositions[id] = fullPositions[id].map((value) => Math.round(value * 100) / 100);
}
writeFileSync(
  FULL_LAYOUT,
  JSON.stringify({ seed: previous.seed ?? SEED, count: nodes.length, edges: edges.length, minGap: GAP, positions: fullPositions }) + "\n",
);
console.log(`[layout] wrote compact graph assets and collision-free layouts`);
