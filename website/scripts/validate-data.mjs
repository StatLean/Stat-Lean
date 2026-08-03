import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import katex from "katex";

const websiteDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const repoDir = path.resolve(websiteDir, "..");
const resultsFile = path.join(websiteDir, "src/data/results.json");
const referencesFile = path.join(websiteDir, "src/data/references.json");
const targetsFile = path.join(websiteDir, "targets.txt");
const graphsDir = path.join(websiteDir, "src/data/graphs");

const categories = new Set([
  "parametric",
  "semiparametric",
  "concentration",
  "highdim",
  "multipletesting",
  "minimaxity",
  "optimization",
  "bayesian",
  "nonparametric",
  "probability",
]);
const resultKinds = new Set(["definition", "theorem", "lemma", "proposition", "corollary", "equation"]);
const nodeKinds = new Set(["root", "repo", "mathlib"]);
const declarationKinds = new Set(["thm", "def"]);
const urlSafeId = /^[A-Za-z0-9][A-Za-z0-9_-]*$/;
const leanName = /^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/;
// Extracted dependency names may contain valid Lean Unicode identifiers and subscripts.
const graphName = /^[^\s./]+(?:\.[^\s./]+)*$/u;
const errors = [];

function fail(location, message) {
  errors.push(`${location}: ${message}`);
}

function isObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, required, optional, location) {
  if (!isObject(value)) {
    fail(location, "expected an object");
    return false;
  }
  const allowed = new Set([...required, ...optional]);
  for (const key of required) {
    if (!Object.hasOwn(value, key)) fail(location, `missing required field ${JSON.stringify(key)}`);
  }
  for (const key of Object.keys(value)) {
    if (!allowed.has(key)) fail(location, `unexpected field ${JSON.stringify(key)}`);
  }
  return true;
}

function nonemptyString(value, location) {
  if (typeof value !== "string" || value.trim().length === 0) {
    fail(location, "expected a nonempty string");
    return false;
  }
  return true;
}

function readJson(file, location) {
  try {
    return JSON.parse(fs.readFileSync(file, "utf8"));
  } catch (error) {
    fail(location, `cannot parse JSON: ${error.message}`);
    return null;
  }
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

// Remove nested Lean comments while preserving line breaks for declaration matching.
function stripLeanComments(source) {
  let result = "";
  let depth = 0;
  let inString = false;
  for (let i = 0; i < source.length; i += 1) {
    const pair = source.slice(i, i + 2);
    if (depth > 0) {
      if (pair === "/-") {
        depth += 1;
        result += "  ";
        i += 1;
      } else if (pair === "-/") {
        depth -= 1;
        result += "  ";
        i += 1;
      } else {
        result += source[i] === "\n" ? "\n" : " ";
      }
      continue;
    }
    if (!inString && pair === "/-") {
      depth = 1;
      result += "  ";
      i += 1;
    } else if (!inString && pair === "--") {
      const end = source.indexOf("\n", i);
      if (end === -1) {
        result += " ".repeat(source.length - i);
        break;
      }
      result += " ".repeat(end - i) + "\n";
      i = end;
    } else {
      result += source[i];
      if (source[i] === '"' && source[i - 1] !== "\\") inString = !inString;
    }
  }
  return result;
}

function sourceDeclares(source, name) {
  const qualifiedPrefix = "(?:[A-Za-z_][A-Za-z0-9_']*\\.)*";
  const modifiers = "(?:(?:private|protected|noncomputable|unsafe|partial|opaque)\\s+)*";
  const commands = "(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)";
  const universes = "(?:\\.\\{[^}\\n]+\\})?";
  const pattern = new RegExp(
    `^\\s*${modifiers}${commands}\\s+${qualifiedPrefix}${escapeRegExp(name)}${universes}(?=\\s|[:{(])`,
    "m",
  );
  return pattern.test(stripLeanComments(source));
}

function validateMath(text, location) {
  const masked = [...text];
  const parse = (tex, displayMode, offset) => {
    try {
      katex.renderToString(tex, { displayMode, throwOnError: true, strict: false });
    } catch (error) {
      fail(`${location}@${offset}`, `KaTeX parse failed: ${error.message}`);
    }
  };

  for (const match of text.matchAll(/\$\$([\s\S]+?)\$\$/g)) {
    parse(match[1], true, match.index);
    for (let i = match.index; i < match.index + match[0].length; i += 1) masked[i] = " ";
  }
  const withoutDisplay = masked.join("");
  for (const match of withoutDisplay.matchAll(/\$([^$\n]+?)\$/g)) {
    parse(match[1], false, match.index);
    for (let i = match.index; i < match.index + match[0].length; i += 1) masked[i] = " ";
  }
  if (masked.includes("$")) fail(location, "contains an unmatched math delimiter '$'");
}

// This deliberately mirrors renderLean: hypotheses claim the first occurrence
// of their token that does not overlap a range already claimed by an earlier item.
function validateTokenAllocation(signature, hypotheses, location) {
  const used = [];
  for (const hypothesis of hypotheses) {
    if (!isObject(hypothesis) || typeof hypothesis.leanToken !== "string" || hypothesis.leanToken.length === 0) continue;
    let from = 0;
    let found = null;
    while (from <= signature.length) {
      const start = signature.indexOf(hypothesis.leanToken, from);
      if (start < 0) break;
      const end = start + hypothesis.leanToken.length;
      if (!used.some(([usedStart, usedEnd]) => start < usedEnd && end > usedStart)) {
        found = [start, end];
        break;
      }
      from = start + 1;
    }
    if (found === null) {
      fail(`${location}.${hypothesis.id ?? "?"}.leanToken`, "is absent from leanSignature or shadowed by an earlier token");
    } else {
      used.push(found);
    }
  }
}

function validateDataLinks(informal, hypotheses, location) {
  const linkTags = [...informal.matchAll(/<([A-Za-z][A-Za-z0-9-]*)\b[^>]*\bdata-link\s*=\s*["']([^"']+)["'][^>]*>/gi)];
  const rawAttributes = [...informal.matchAll(/\bdata-link\s*=/gi)];
  if (linkTags.length !== rawAttributes.length) {
    fail(location, "every data-link must be a quoted attribute on an HTML tag");
  }
  const counts = new Map();
  for (const match of linkTags) {
    const id = match[2];
    counts.set(id, (counts.get(id) ?? 0) + 1);
  }
  const hypothesisIds = new Set(hypotheses.filter(isObject).map((hypothesis) => hypothesis.id));
  for (const [id, count] of counts) {
    if (!hypothesisIds.has(id)) fail(location, `data-link ${JSON.stringify(id)} has no hypothesis`);
    if (count !== 1) fail(location, `data-link ${JSON.stringify(id)} occurs ${count} times; expected exactly once`);
  }
}

function parseTargets() {
  let text;
  try {
    text = fs.readFileSync(targetsFile, "utf8");
  } catch (error) {
    fail("targets.txt", `cannot read file: ${error.message}`);
    return [];
  }
  const lines = text.replace(/\r\n/g, "\n").split("\n");
  if (lines.at(-1) === "") lines.pop();
  const targets = [];
  for (let index = 0; index < lines.length; index += 1) {
    const location = `targets.txt:${index + 1}`;
    const line = lines[index];
    if (line.length === 0) {
      fail(location, "blank target rows are not allowed");
      continue;
    }
    const parts = line.split("\t");
    if (parts.length !== 2) {
      fail(location, "expected exactly <id>\\t<fullName>");
      continue;
    }
    const [id, fullName] = parts;
    if (id !== id.trim() || fullName !== fullName.trim()) fail(location, "fields must not have surrounding whitespace");
    if (!urlSafeId.test(id)) fail(`${location}.id`, "must be URL-safe (letters, digits, '_' and '-' only)");
    if (!leanName.test(fullName)) fail(`${location}.fullName`, "is not a valid dotted Lean name");
    targets.push({ id, fullName });
  }
  const seenIds = new Set();
  const seenNames = new Set();
  for (const target of targets) {
    if (seenIds.has(target.id)) fail("targets.txt", `duplicate id ${JSON.stringify(target.id)}`);
    if (seenNames.has(target.fullName)) fail("targets.txt", `duplicate fullName ${JSON.stringify(target.fullName)}`);
    seenIds.add(target.id);
    seenNames.add(target.fullName);
  }
  return targets;
}

const resultRequiredKeys = [
  "id", "category", "kind", "leanName", "fullName", "title", "citation", "file", "docGenUrl",
  "informal", "summary", "leanSignature", "hypotheses", "hasGraph",
];
const hypothesisRequiredKeys = ["id", "leanToken", "label"];

const referencesValue = readJson(referencesFile, "references.json");
const references = Array.isArray(referencesValue) ? referencesValue : [];
if (!Array.isArray(referencesValue)) fail("references.json", "top-level value must be an array");
const referenceKeys = new Set();
for (let index = 0; index < references.length; index += 1) {
  const reference = references[index];
  const location = `references.json[${index}]`;
  if (!exactKeys(reference, ["key", "sortKey", "html"], [], location)) continue;
  for (const field of ["key", "sortKey", "html"]) nonemptyString(reference[field], `${location}.${field}`);
  if (!urlSafeId.test(reference.key)) fail(`${location}.key`, "must be URL-safe");
  if (referenceKeys.has(reference.key)) fail(`${location}.key`, `duplicate key ${JSON.stringify(reference.key)}`);
  referenceKeys.add(reference.key);
  if (typeof reference.html === "string") validateMath(reference.html, `${location}.html`);
}

const resultsValue = readJson(resultsFile, "results.json");
const results = Array.isArray(resultsValue) ? resultsValue : [];
if (!Array.isArray(resultsValue)) fail("results.json", "top-level value must be an array");

const resultIds = new Set();
const resultFullNames = new Set();
for (let index = 0; index < results.length; index += 1) {
  const result = results[index];
  const location = `results.json[${index}]`;
  if (!exactKeys(result, resultRequiredKeys, ["formalizationNotes", "shortRef", "reference"], location)) continue;

  for (const field of ["id", "category", "kind", "leanName", "fullName", "title", "citation", "file", "docGenUrl", "informal", "summary", "leanSignature"]) {
    nonemptyString(result[field], `${location}.${field}`);
  }
  if (!urlSafeId.test(result.id)) fail(`${location}.id`, "must be URL-safe (letters, digits, '_' and '-' only)");
  if (resultIds.has(result.id)) fail(`${location}.id`, `duplicate id ${JSON.stringify(result.id)}`);
  resultIds.add(result.id);
  if (!categories.has(result.category)) fail(`${location}.category`, `unknown category ${JSON.stringify(result.category)}`);
  if (!resultKinds.has(result.kind)) fail(`${location}.kind`, `unknown result kind ${JSON.stringify(result.kind)}`);
  if (!leanName.test(result.fullName)) fail(`${location}.fullName`, "is not a valid dotted Lean name");
  if (resultFullNames.has(result.fullName)) fail(`${location}.fullName`, `duplicate fullName ${JSON.stringify(result.fullName)}`);
  resultFullNames.add(result.fullName);
  if (typeof result.hasGraph !== "boolean") fail(`${location}.hasGraph`, "expected a boolean");
  if (Object.hasOwn(result, "formalizationNotes")) {
    if (nonemptyString(result.formalizationNotes, `${location}.formalizationNotes`)) {
      validateMath(result.formalizationNotes, `${location}.formalizationNotes`);
    }
  }
  if (Object.hasOwn(result, "shortRef") && nonemptyString(result.shortRef, `${location}.shortRef`)) {
    validateMath(result.shortRef, `${location}.shortRef`);
  }
  if (Object.hasOwn(result, "reference")) {
    const referenceLocation = `${location}.reference`;
    if (exactKeys(result.reference, ["formal", "pointer", "keys"], ["biblio"], referenceLocation)) {
      for (const field of ["formal", "pointer"]) {
        if (nonemptyString(result.reference[field], `${referenceLocation}.${field}`)) {
          validateMath(result.reference[field], `${referenceLocation}.${field}`);
        }
      }
      if (Object.hasOwn(result.reference, "biblio")
          && nonemptyString(result.reference.biblio, `${referenceLocation}.biblio`)) {
        validateMath(result.reference.biblio, `${referenceLocation}.biblio`);
      }
      if (!Array.isArray(result.reference.keys) || result.reference.keys.length === 0) {
        fail(`${referenceLocation}.keys`, "expected a nonempty array");
      } else {
        const seenKeys = new Set();
        for (let keyIndex = 0; keyIndex < result.reference.keys.length; keyIndex += 1) {
          const key = result.reference.keys[keyIndex];
          const keyLocation = `${referenceLocation}.keys[${keyIndex}]`;
          if (!nonemptyString(key, keyLocation)) continue;
          if (!urlSafeId.test(key)) fail(keyLocation, "must be URL-safe");
          if (seenKeys.has(key)) fail(keyLocation, `duplicate key ${JSON.stringify(key)}`);
          if (!referenceKeys.has(key)) fail(keyLocation, `unknown reference key ${JSON.stringify(key)}`);
          seenKeys.add(key);
        }
      }
    }
  }
  if (typeof result.informal === "string") validateMath(result.informal, `${location}.informal`);

  const hypotheses = Array.isArray(result.hypotheses) ? result.hypotheses : [];
  if (!Array.isArray(result.hypotheses)) fail(`${location}.hypotheses`, "expected an array");
  const hypothesisIds = new Set();
  for (let hypothesisIndex = 0; hypothesisIndex < hypotheses.length; hypothesisIndex += 1) {
    const hypothesis = hypotheses[hypothesisIndex];
    const hypothesisLocation = `${location}.hypotheses[${hypothesisIndex}]`;
    if (!exactKeys(hypothesis, hypothesisRequiredKeys, ["note"], hypothesisLocation)) continue;
    for (const field of hypothesisRequiredKeys) nonemptyString(hypothesis[field], `${hypothesisLocation}.${field}`);
    if (Object.hasOwn(hypothesis, "note")) nonemptyString(hypothesis.note, `${hypothesisLocation}.note`);
    if (!urlSafeId.test(hypothesis.id)) fail(`${hypothesisLocation}.id`, "must be URL-safe");
    if (hypothesisIds.has(hypothesis.id)) fail(`${hypothesisLocation}.id`, `duplicate hypothesis id ${JSON.stringify(hypothesis.id)}`);
    hypothesisIds.add(hypothesis.id);
  }
  if (typeof result.informal === "string") validateDataLinks(result.informal, hypotheses, `${location}.informal`);

  if (typeof result.file === "string") {
    const normalized = path.posix.normalize(result.file);
    const validSourcePath = normalized === result.file
      && result.file.startsWith("StatLean/")
      && result.file.endsWith(".lean")
      && !path.posix.isAbsolute(result.file);
    if (!validSourcePath) {
      fail(`${location}.file`, "must be a normalized repository-relative StatLean/*.lean path");
    } else {
      const sourceFile = path.resolve(repoDir, result.file);
      if (!sourceFile.startsWith(`${repoDir}${path.sep}`) || !fs.existsSync(sourceFile) || !fs.statSync(sourceFile).isFile()) {
        fail(`${location}.file`, `source file does not exist: ${result.file}`);
      } else if (typeof result.leanName === "string") {
        const source = fs.readFileSync(sourceFile, "utf8");
        if (!sourceDeclares(source, result.leanName)) {
          fail(`${location}.leanName`, `declaration ${JSON.stringify(result.leanName)} is not present in ${result.file}`);
        }
      }
      const expectedDocUrl = `../docs/${result.file.slice(0, -".lean".length)}.html#${result.fullName}`;
      if (result.docGenUrl !== expectedDocUrl) {
        fail(`${location}.docGenUrl`, `expected ${JSON.stringify(expectedDocUrl)}`);
      }
    }
  }
}

const targets = parseTargets();
const expectedTargets = results.filter((result) => isObject(result) && result.hasGraph === true);
if (targets.length !== expectedTargets.length) {
  fail("targets.txt", `has ${targets.length} rows, expected ${expectedTargets.length} hasGraph result rows`);
}
for (let index = 0; index < Math.max(targets.length, expectedTargets.length); index += 1) {
  const target = targets[index];
  const result = expectedTargets[index];
  if (target === undefined || result === undefined) continue;
  if (target.id !== result.id || target.fullName !== result.fullName) {
    fail(`targets.txt:${index + 1}`, `must match results order exactly; expected ${result.id}\\t${result.fullName}`);
  }
}

let graphFiles = [];
try {
  graphFiles = fs.readdirSync(graphsDir).filter((file) => file.endsWith(".json")).sort();
} catch (error) {
  fail("graphs", `cannot read graph directory: ${error.message}`);
}
const expectedGraphFiles = expectedTargets.map((result) => `${result.id}.json`).sort();
for (const file of graphFiles) {
  if (!expectedGraphFiles.includes(file)) fail(`graphs/${file}`, "has no matching result with hasGraph=true");
}
for (const file of expectedGraphFiles) {
  if (!graphFiles.includes(file)) fail(`graphs/${file}`, "missing graph for result with hasGraph=true");
}

const resultById = new Map(expectedTargets.map((result) => [result.id, result]));
for (const file of graphFiles) {
  const id = file.slice(0, -".json".length);
  const result = resultById.get(id);
  const location = `graphs/${file}`;
  const graph = readJson(path.join(graphsDir, file), location);
  if (!exactKeys(graph, ["root", "nodes", "edges"], [], location)) continue;
  nonemptyString(graph.root, `${location}.root`);
  if (result !== undefined && graph.root !== result.fullName) fail(`${location}.root`, `expected ${JSON.stringify(result.fullName)}`);
  if (!Array.isArray(graph.nodes)) fail(`${location}.nodes`, "expected an array");
  if (!Array.isArray(graph.edges)) fail(`${location}.edges`, "expected an array");
  const nodes = Array.isArray(graph.nodes) ? graph.nodes : [];
  const edges = Array.isArray(graph.edges) ? graph.edges : [];
  if (nodes.length === 0) fail(`${location}.nodes`, "must be nonempty");
  const nodeIds = new Set();
  const nodeFullNames = new Set();
  let rootNodes = 0;
  for (let nodeIndex = 0; nodeIndex < nodes.length; nodeIndex += 1) {
    const node = nodes[nodeIndex];
    const nodeLocation = `${location}.nodes[${nodeIndex}]`;
    if (!exactKeys(node, ["id", "label", "full", "kind", "decl", "module"], [], nodeLocation)) continue;
    for (const field of ["id", "label", "full", "kind", "decl", "module"]) nonemptyString(node[field], `${nodeLocation}.${field}`);
    if (!graphName.test(node.id)) fail(`${nodeLocation}.id`, "is not a valid dotted Lean name");
    if (!graphName.test(node.full)) fail(`${nodeLocation}.full`, "is not a valid dotted Lean name");
    if (!leanName.test(node.module)) fail(`${nodeLocation}.module`, "is not a valid dotted Lean module name");
    if (node.id !== node.full) fail(nodeLocation, "id and full must be identical");
    if (node.label !== node.full.split(".").at(-1)) fail(`${nodeLocation}.label`, "must be the final component of full");
    if (!nodeKinds.has(node.kind)) fail(`${nodeLocation}.kind`, `unknown node kind ${JSON.stringify(node.kind)}`);
    if (!declarationKinds.has(node.decl)) fail(`${nodeLocation}.decl`, `unknown declaration kind ${JSON.stringify(node.decl)}`);
    if (nodeIds.has(node.id)) fail(`${nodeLocation}.id`, `duplicate node id ${JSON.stringify(node.id)}`);
    if (nodeFullNames.has(node.full)) fail(`${nodeLocation}.full`, `duplicate node full name ${JSON.stringify(node.full)}`);
    nodeIds.add(node.id);
    nodeFullNames.add(node.full);
    if (node.kind === "root") rootNodes += 1;
    if (nodeIndex === 0 && (node.kind !== "root" || node.id !== graph.root)) {
      fail(nodeLocation, "first node must be the graph root");
    }
    if (node.kind === "repo" && !node.module.startsWith("StatLean")) {
      fail(`${nodeLocation}.module`, "repo nodes must come from a StatLean module");
    }
    if (node.kind === "mathlib" && node.module.startsWith("StatLean")) {
      fail(`${nodeLocation}.module`, "Mathlib nodes cannot come from a StatLean module");
    }
  }
  if (rootNodes !== 1) fail(`${location}.nodes`, `expected exactly one root node, found ${rootNodes}`);
  if (result !== undefined && nodes[0]?.module !== result.file.slice(0, -".lean".length).replaceAll("/", ".")) {
    fail(`${location}.nodes[0].module`, "must match the result source file module");
  }

  const seenEdges = new Set();
  const adjacency = new Map();
  for (let edgeIndex = 0; edgeIndex < edges.length; edgeIndex += 1) {
    const edge = edges[edgeIndex];
    const edgeLocation = `${location}.edges[${edgeIndex}]`;
    if (!exactKeys(edge, ["source", "target"], [], edgeLocation)) continue;
    nonemptyString(edge.source, `${edgeLocation}.source`);
    nonemptyString(edge.target, `${edgeLocation}.target`);
    if (!nodeIds.has(edge.source)) fail(`${edgeLocation}.source`, `dangling source ${JSON.stringify(edge.source)}`);
    if (!nodeIds.has(edge.target)) fail(`${edgeLocation}.target`, `dangling target ${JSON.stringify(edge.target)}`);
    if (edge.source === edge.target) fail(edgeLocation, "self-edges are not allowed");
    const key = `${edge.source}\u0000${edge.target}`;
    if (seenEdges.has(key)) fail(edgeLocation, "duplicate edge");
    seenEdges.add(key);
    if (nodeIds.has(edge.source) && nodeIds.has(edge.target)) {
      if (!adjacency.has(edge.source)) adjacency.set(edge.source, []);
      adjacency.get(edge.source).push(edge.target);
    }
    const sourceNode = nodes.find((node) => isObject(node) && node.id === edge.source);
    if (sourceNode?.kind === "mathlib") fail(`${edgeLocation}.source`, "Mathlib nodes must remain dependency leaves");
  }

  const reachable = new Set();
  const pending = [graph.root];
  while (pending.length > 0) {
    const current = pending.pop();
    if (reachable.has(current)) continue;
    reachable.add(current);
    for (const target of adjacency.get(current) ?? []) {
      if (!reachable.has(target)) pending.push(target);
    }
  }
  for (let nodeIndex = 0; nodeIndex < nodes.length; nodeIndex += 1) {
    const node = nodes[nodeIndex];
    if (isObject(node) && typeof node.id === "string" && !reachable.has(node.id)) {
      fail(`${location}.nodes[${nodeIndex}]`, `node ${JSON.stringify(node.id)} is unreachable from graph.root`);
    }
  }
}

if (errors.length > 0) {
  console.error(`Data validation failed with ${errors.length} error${errors.length === 1 ? "" : "s"}:`);
  for (const error of errors) console.error(`  - ${error}`);
  process.exitCode = 1;
} else {
  console.log(`Validated ${results.length} results, ${targets.length} targets, and ${graphFiles.length} dependency graphs.`);
}
