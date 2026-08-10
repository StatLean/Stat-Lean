#!/usr/bin/env node
/**
 * Merge authored `website/incoming/<area>.results.json` + `<area>.refs.json`
 * batches into the site data, then delete the incoming files.
 *
 * Lanes author into `incoming/` rather than editing `results.json` directly so
 * that several areas can be written in parallel without conflicting on one
 * 2 MB file. This script is the single place that knows how to fold them in:
 *
 *   - results are appended to `src/data/results.json` (ids must be unique);
 *   - `targets.txt` gains one `<id>\t<fullName>` row per `hasGraph` result,
 *     in the same order as `results.json` — the validator enforces this;
 *   - references are added to `src/data/references.json` if the key is new,
 *     and the array is re-sorted by `sortKey`;
 *   - a `_chapters` key in a refs batch is folded into `src/lib/bookChapters.ts`
 *     (both `CHAPTER_TITLES` and `TEXTBOOK_KEYS`).
 *
 * Usage: node scripts/merge-incoming.mjs [--dry]
 */
import { readFileSync, writeFileSync, readdirSync, existsSync, rmSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = join(HERE, "..");
const INCOMING = join(ROOT, "incoming");
const RESULTS = join(ROOT, "src", "data", "results.json");
const REFS = join(ROOT, "src", "data", "references.json");
const TARGETS = join(ROOT, "targets.txt");
const CHAPTERS = join(ROOT, "src", "lib", "bookChapters.ts");

const DRY = process.argv.includes("--dry");
const readJson = (p) => JSON.parse(readFileSync(p, "utf8"));
const writeJson = (p, v) =>
  writeFileSync(p, JSON.stringify(v, null, 2) + "\n");

if (!existsSync(INCOMING)) {
  console.log("[merge] nothing to do: no incoming/ directory");
  process.exit(0);
}

const results = readJson(RESULTS);
const refs = readJson(REFS);
const byId = new Set(results.map((r) => r.id));
const refKeys = new Set(refs.map((r) => r.key));

const resultFiles = readdirSync(INCOMING).filter((f) => f.endsWith(".results.json")).sort();
const refFiles = readdirSync(INCOMING).filter((f) => f.endsWith(".refs.json")).sort();

let added = 0;
const chapterAdds = {};

for (const f of resultFiles) {
  const batch = readJson(join(INCOMING, f));
  let n = 0;
  for (const r of batch) {
    if (byId.has(r.id)) {
      console.warn(`[merge]   ! duplicate id skipped: ${r.id}`);
      continue;
    }
    byId.add(r.id);
    // lanes were briefed with `alsoIn` before the repo settled on `crossListed`
    // (upstream's name, already used by the RKHS / exponential-family batch);
    // normalise here so only one field ever reaches the site data.
    if (r.alsoIn) {
      const merged = new Set([...(r.crossListed || []), ...r.alsoIn]);
      r.crossListed = [...merged].sort();
      delete r.alsoIn;
    }
    results.push(r);
    n++;
  }
  added += n;
  console.log(`[merge] ${f}: +${n} results`);
}

for (const f of refFiles) {
  const batch = readJson(join(INCOMING, f));
  const arr = Array.isArray(batch) ? batch : batch.refs || [];
  const chapters = Array.isArray(batch) ? null : batch._chapters;
  let n = 0;
  for (const r of arr) {
    if (!r || !r.key) continue;
    if (r.key === "_chapters") continue;
    if (refKeys.has(r.key)) continue;
    refKeys.add(r.key);
    refs.push(r);
    n++;
  }
  if (chapters) Object.assign(chapterAdds, chapters);
  console.log(`[merge] ${f}: +${n} references`);
}

refs.sort((a, b) =>
  (a.sortKey || "").localeCompare(b.sortKey || "") || a.key.localeCompare(b.key),
);

// targets.txt: rebuild from results order, one row per hasGraph result
const targetRows = results
  .filter((r) => r.hasGraph)
  .map((r) => `${r.id}\t${r.fullName}`);

// bookChapters.ts: fold in any new chapter maps
let chaptersSrc = readFileSync(CHAPTERS, "utf8");
const newBooks = Object.keys(chapterAdds);
if (newBooks.length) {
  for (const key of newBooks) {
    if (!chaptersSrc.includes(`  ${key}: {`) && !chaptersSrc.includes(`  "${key}": {`)) {
      const titles = chapterAdds[key];
      const body = Object.entries(titles)
        .sort((a, b) => Number(a[0]) - Number(b[0]))
        .map(([n, t]) => `    ${n}: ${JSON.stringify(t)},`)
        .join("\n");
      const entry = `  ${JSON.stringify(key)}: {\n${body}\n  },\n`;
      const anchor = "const CHAPTER_TITLES: Record<string, Record<number, string>> = {\n";
      chaptersSrc = chaptersSrc.replace(anchor, anchor + entry);
      console.log(`[merge] bookChapters: + ${key} (${Object.keys(titles).length} chapters)`);
    }
    // ensure it is treated as a textbook (gets the chapter-ordered TOC)
    if (!chaptersSrc.includes(`"${key}",`)) {
      chaptersSrc = chaptersSrc.replace(
        "export const TEXTBOOK_KEYS = new Set([\n",
        `export const TEXTBOOK_KEYS = new Set([\n  ${JSON.stringify(key)},\n`,
      );
    }
  }
}

console.log(
  `[merge] totals → results ${results.length} (+${added}), refs ${refs.length}, targets ${targetRows.length}`,
);

if (DRY) {
  console.log("[merge] --dry: nothing written");
  process.exit(0);
}

writeJson(RESULTS, results);
writeJson(REFS, refs);
writeFileSync(TARGETS, targetRows.join("\n") + "\n");
writeFileSync(CHAPTERS, chaptersSrc);
rmSync(INCOMING, { recursive: true, force: true });
console.log("[merge] wrote results.json, references.json, targets.txt, bookChapters.ts");
console.log("[merge] removed incoming/");
