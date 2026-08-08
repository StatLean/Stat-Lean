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

/** Abbreviation printed for each kind of cited item. */
const KIND_SHORT: [RegExp, string][] = [
  [/^theorems?$|^thms?$/i, "Thm"],
  [/^lemmas?$/i, "Lem"],
  [/^corollar(?:y|ies)$|^cors?$/i, "Cor"],
  [/^propositions?$|^props?$/i, "Prop"],
  [/^definitions?$|^defs?$/i, "Def"],
  [/^examples?$/i, "Ex"],
  [/^equations?$|^eqs?$/i, "Eq"],
];

function shortKind(word: string): string {
  for (const [re, short] of KIND_SHORT) if (re.test(word)) return short;
  return "";
}

/**
 * Parse a `reference.pointer` string into { chapter, order, itemLabel }.
 *
 * Books differ in how they number results. Most (van der Vaart, Wainwright,
 * Lu) number them `chapter.item`, and Lehmann–Romano numbers them
 * `chapter.section.item`, so the number itself says which chapter it is in.
 * Lehmann–Casella instead numbers them `section.item`, restarting at each
 * section — its Theorem 5.8 is the eighth result of Chapter 1's fifth section,
 * and Chapter 2 has a *different* Theorem 5.8. A bare "Thm 5.8" printed under
 * "Chapter 1" therefore reads as an error, and the chapter cannot be recovered
 * from the number. So: take the chapter from the pointer's own "Chapter N" or
 * "§C.S" locator rather than from the result number, and print the section
 * alongside any number that does not already begin with the chapter.
 */
export function parsePointer(pointer: string): {
  chapter: number | null;
  order: number;
  itemLabel: string;
} {
  const p = pointer || "";
  // A pointer may append a cross-reference to another book ("…; Lehmann–Romano
  // (2022), Theorem 2.6.2"); only the leading segment locates it in *this* book.
  const head = p.split(/;\s/)[0]!;

  const chapterMatch = head.match(/(?:Chapter|Lecture)\s+(\d+)/i);
  const sectionMatch = head.match(/§\s*(\d+)\.(\d+)/);
  // Result numbers, read after removing the chapter/section locator so that
  // "§1.5" is not mistaken for the number of a result.
  const body = head
    .replace(/(?:Chapter|Lecture)\s+\d+/gi, "")
    .replace(/§\s*\d+(?:\.\d+)*/g, "");
  const nums = [...body.matchAll(/(\d+)\.(\d+)(?:\.(\d+))?/g)];
  const num = nums[0];

  let chapter: number | null = null;
  let section: number | null = null;
  if (chapterMatch) chapter = +chapterMatch[1]!;
  if (sectionMatch) {
    chapter ??= +sectionMatch[1]!;
    section = +sectionMatch[2]!;
  }
  if (chapter == null && num) chapter = +num[1]!;
  if (chapter == null) {
    const bare = head.match(/§\s*(\d+)/);
    if (bare) chapter = +bare[1]!;
  }
  // A `chapter.section.item` number carries its own section.
  if (section == null && num?.[3] !== undefined) section = +num[2]!;

  // Sort key within the chapter: by section, then by result number.
  const order = num
    ? (section ?? +num[1]!) * 1e3 + +num[2]! + +(num[3] ?? 0) / 1e3
    : (section ?? chapter ?? 0) * 1e3;

  // Read the *first* "<kind> <number>" pair, so a pointer naming several items
  // ("Definition 1.24 and Theorem 1.27") labels itself with the one it leads on
  // rather than with whichever kind word happens to come first in TYPE_MAP.
  const cited = body.match(
    /(Theorems?|Thms?|Lemmas?|Corollar(?:y|ies)|Cors?|Propositions?|Props?|Definitions?|Defs?|Examples?|Equations?|Eqs?)\.?\s*\(?(\d+\.\d+(?:\.\d+)?)\)?(?:\s*[–-]\s*\(?(\d+\.\d+)\)?)?/i,
  );
  const typeShort = cited ? shortKind(cited[1]!) : "";

  const numLabel = cited
    ? cited[2]! + (cited[3] ? `–${cited[3]}` : "")
    : (num?.[0] ?? "");
  let itemLabel: string;
  if (typeShort && numLabel) {
    itemLabel =
      typeShort === "Eq"
        ? `Eq. ${numLabel.split("–").map((n) => `(${n})`).join("–")}`
        : `${typeShort} ${numLabel}`;
  } else if (numLabel) {
    itemLabel = `§${numLabel}`;
  } else {
    const s = head.match(/§\s*([\d.]+)/);
    itemLabel = s ? `§${s[1]}` : head;
  }
  // A number is section-scoped when the pointer locates it in "§C.S" and the
  // number restarts at that section — Lehmann–Casella's "§1.5, Theorem 5.8".
  // A three-part number ("3.2.1") already names its chapter and section, and a
  // number with no "§C.S" locator is chapter-scoped; neither gets a prefix.
  const sectionScoped =
    cited != null &&
    sectionMatch != null &&
    cited[2]!.split(".").length === 2 &&
    +cited[2]!.split(".")[0]! === +sectionMatch[2]!;
  if (sectionScoped) itemLabel = `§${sectionMatch![1]}.${sectionMatch![2]} ${itemLabel}`;
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
