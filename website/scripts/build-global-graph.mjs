// Merge the per-result dependency graphs into one compact global graph, at build
// time, so the browser neither ships 450 JSON files nor unions them on every visit.
//
// The compact form drops what is derivable and interns what repeats:
//   * `id` is always identical to `full`      (enforced by validate-data.mjs)
//   * `label` is always full.split(".").at(-1) (enforced by validate-data.mjs)
//   * `module` strings repeat across thousands of nodes -> interned into a table
//   * edges reference nodes by index rather than by dotted name
//
// Result: ~2.4 MB of merged JSON becomes ~390 KB (~80 KB gzipped).
//
// It also runs the force-directed layout here rather than in the browser. The
// graph is fixed, so its layout is fixed; computing it on every visit cost ~2.8 s
// of blocked main thread for the default view, and over ten minutes once Mathlib
// nodes were added. Positions ship as integers and the page just places them.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import cytoscape from "cytoscape";
import fcose from "cytoscape-fcose";

cytoscape.use(fcose);

const websiteDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const graphsDir = path.join(websiteDir, "src/data/graphs");
const outFile = path.join(websiteDir, "src/data/global-graph.json");

const nodes = new Map(); // full -> { kind, decl, module }
const edges = new Set(); // "source\ttarget"

const files = fs.readdirSync(graphsDir).filter((f) => f.endsWith(".json")).sort();
for (const file of files) {
  const g = JSON.parse(fs.readFileSync(path.join(graphsDir, file), "utf8"));
  for (const n of g.nodes) {
    // A node that roots its own graph is just a repo node in the global union.
    const kind = n.kind === "root" ? "repo" : n.kind;
    const prev = nodes.get(n.full);
    if (!prev) nodes.set(n.full, { kind, decl: n.decl, module: n.module });
    else if (prev.kind === "mathlib" && kind === "repo") prev.kind = "repo";
  }
  for (const e of g.edges) edges.add(`${e.source}\t${e.target}`);
}

const fulls = [...nodes.keys()].sort();
const index = new Map(fulls.map((f, i) => [f, i]));
const modules = [...new Set(fulls.map((f) => nodes.get(f).module))].sort();
const moduleIndex = new Map(modules.map((m, i) => [m, i]));

const compact = {
  modules,
  // [full, isRepo, isDef, moduleIndex]
  nodes: fulls.map((f) => {
    const n = nodes.get(f);
    return [f, n.kind === "repo" ? 1 : 0, n.decl === "def" ? 1 : 0, moduleIndex.get(n.module)];
  }),
  edges: [...edges]
    .map((s) => s.split("\t"))
    .filter(([a, b]) => index.has(a) && index.has(b))
    .map(([a, b]) => [index.get(a), index.get(b)])
    .sort((x, y) => x[0] - y[0] || x[1] - y[1]),
};

/**
 * Lay out the subgraph induced by `keep` and return flat [x, y, x, y, …] in the
 * order of `keep`. The page shows two graphs — repo-only by default, everything
 * when Mathlib is switched on — and each needs its own layout.
 *
 * `quality` trades layout time against tidiness. The repo graph is small enough
 * for fcose's full refinement pass; the 3682-node full graph is not (that pass
 * does not finish in ten minutes), so it gets the spectral draft.
 */
async function layout(keep, quality) {
  const keepSet = new Set(keep);
  const cy = cytoscape({
    headless: true,
    styleEnabled: true,
    elements: [
      ...keep.map((i) => ({ data: { id: fulls[i] } })),
      ...compact.edges
        .filter(([a, b]) => keepSet.has(a) && keepSet.has(b))
        .map(([a, b]) => ({ data: { id: `${b}~${a}`, source: fulls[b], target: fulls[a] } })),
    ],
  });
  await new Promise((resolve) => {
    const l = cy.layout({
      name: "fcose",
      quality,
      animate: false,
      randomize: true,
      fit: true,
      padding: 50,
      packComponents: false,
      nodeSeparation: 60,
      idealEdgeLength: 42,
      nodeRepulsion: 7000,
      gravity: 0.4,
      gravityRange: 3,
      numIter: 600,
    });
    l.one("layoutstop", resolve);
    l.run();
  });
  const out = [];
  for (const i of keep) {
    const p = cy.getElementById(fulls[i]).position();
    out.push(Math.round(p.x), Math.round(p.y));
  }
  cy.destroy();
  return out;
}

const allIdx = fulls.map((_, i) => i);
const repoIdx = allIdx.filter((i) => compact.nodes[i][1] === 1);
const t0 = Date.now();
compact.repoLayout = await layout(repoIdx, "default");
compact.fullLayout = await layout(allIdx, "draft");
const layoutSecs = ((Date.now() - t0) / 1000).toFixed(1);

// The page indexes these flat arrays positionally, so a length or finiteness
// slip would silently stack nodes at the origin rather than fail.
const assert = (ok, msg) => {
  if (!ok) {
    console.error(`build-global-graph: ${msg}`);
    process.exit(1);
  }
};
assert(compact.fullLayout.length === 2 * allIdx.length, "fullLayout length");
assert(compact.repoLayout.length === 2 * repoIdx.length, "repoLayout length");
assert(
  [...compact.fullLayout, ...compact.repoLayout].every(Number.isFinite),
  "non-finite coordinate in a layout",
);

fs.writeFileSync(outFile, JSON.stringify(compact));
const kb = (n) => `${Math.round(n / 1024)} KB`;
console.log(
  `global graph: ${compact.nodes.length} nodes, ${compact.edges.length} edges, ` +
    `${modules.length} modules, layouts precomputed in ${layoutSecs}s ` +
    `-> ${kb(fs.statSync(outFile).size)}`,
);
