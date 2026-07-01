import type { CategoryId } from "./types";
import { RESULTS } from "./data";

/** A result that cites a given reference. */
export interface Citing {
  id: string;
  title: string;
  category: CategoryId;
  /** true when this reference is the result's primary source (keys[0]); its
   *  `pointer` is in this book's numbering, so it can be placed in the TOC. */
  isPrimary: boolean;
  /** parsed chapter number of the result within the primary book (null = unparsed). */
  chapter: number | null;
  /** sort key within a chapter (chapter.section.item as a single number). */
  order: number;
  /** concise locator label, e.g. "Thm 7.2", "Eq. (7.1)", "§4.2". */
  itemLabel: string;
}

const TYPE_MAP: [RegExp, string][] = [
  [/\btheorem\b|\bthm\b/i, "Thm"],
  [/\bproposition\b|\bprop\b/i, "Prop"],
  [/\bcorollary\b|\bcor\b/i, "Cor"],
  [/\blemma\b|\blem\b/i, "Lem"],
  [/\bdefinition\b|\bdef\b/i, "Def"],
  [/\bexample\b/i, "Ex"],
  [/\bequation\b|\beq\b/i, "Eq"],
];

/** Parse a `reference.pointer` string into { chapter, order, itemLabel }. */
export function parsePointer(pointer: string): {
  chapter: number | null;
  order: number;
  itemLabel: string;
} {
  const p = pointer || "";
  const nums = [...p.matchAll(/(\d+)\.(\d+)(?:\.(\d+))?/g)];
  let chapter: number | null = null;
  let order = 0;
  let numLabel = "";
  if (nums.length) {
    const last = nums[nums.length - 1];
    chapter = +last[1];
    order = +last[1] + +last[2] / 1e3 + (+(last[3] ?? 0)) / 1e6;
    numLabel = last[0];
  }
  const cm = p.match(/(?:Chapter|Lecture)\s+(\d+)/i);
  if (cm) {
    chapter = +cm[1];
    if (!nums.length) order = +cm[1];
  }
  if (chapter == null) {
    const s = p.match(/§\s*(\d+)/);
    if (s) {
      chapter = +s[1];
      order = +s[1];
    }
  }
  let typeShort = "";
  for (const [re, short] of TYPE_MAP) {
    if (re.test(p)) {
      typeShort = short;
      break;
    }
  }
  let itemLabel: string;
  if (typeShort && numLabel) {
    itemLabel = typeShort === "Eq" ? `Eq. (${numLabel})` : `${typeShort} ${numLabel}`;
  } else if (numLabel) {
    itemLabel = `§${numLabel}`;
  } else {
    const s = p.match(/§\s*([\d.]+)/);
    itemLabel = s ? `§${s[1]}` : p;
  }
  return { chapter, order, itemLabel };
}

/** reference key → the results that cite it (primary + bibliographic-comment cites). */
export const REF_INDEX: Map<string, Citing[]> = (() => {
  const idx = new Map<string, Citing[]>();
  for (const r of RESULTS) {
    const keys = r.reference?.keys ?? [];
    const { chapter, order, itemLabel } = parsePointer(r.reference?.pointer ?? "");
    keys.forEach((key, i) => {
      const list = idx.get(key) ?? [];
      list.push({
        id: r.id,
        title: r.title,
        category: r.category,
        isPrimary: i === 0,
        chapter,
        order,
        itemLabel,
      });
      idx.set(key, list);
    });
  }
  return idx;
})();

export function citingCount(key: string): number {
  return REF_INDEX.get(key)?.length ?? 0;
}
