import type { Reference } from "./types";
import rawRefs from "../data/references.json";

const REF_BY_KEY = new Map((rawRefs as unknown as Reference[]).map((r) => [r.key, r]));

/**
 * Turn the works mentioned in a bibliographic-comments paragraph into links to
 * the references page. For each key cited by the result we locate its author's
 * surname in the prose (disambiguated by the key's year when several works share
 * an author) and wrap that mention in an `<a class="ref-cite" href="#/references#KEY">`.
 * Unmatched keys are simply left unlinked. Injected `<a>` tags are inert to the
 * KaTeX/markdown pass in `renderReference`, so this runs before it.
 */
export function linkifyBiblio(text: string, keys: string[]): string {
  if (!text || !keys?.length) return text;
  const cands = keys
    .map((key) => {
      const ref = REF_BY_KEY.get(key);
      if (!ref?.sortKey) return null;
      const ym = key.match(/(\d{4})/);
      return { key, surname: ref.sortKey, year: ym ? ym[1] : null };
    })
    .filter((c): c is { key: string; surname: string; year: string | null } => !!c)
    // year-specific keys claim their occurrence first; longer surnames before shorter.
    .sort(
      (a, b) => (b.year ? 1 : 0) - (a.year ? 1 : 0) || b.surname.length - a.surname.length,
    );

  const claimed: [number, number][] = [];
  const overlaps = (s: number, e: number) =>
    claimed.some(([cs, ce]) => s < ce && e > cs);
  const isLetter = /\p{L}/u;
  // A surname match must sit on word boundaries so "Lu" doesn't match inside
  // "Lugosi", "Le Cam" doesn't match inside a longer token, etc.
  const onBoundary = (start: number, end: number) => {
    const before = start > 0 ? text[start - 1] : " ";
    const after = end < text.length ? text[end] : " ";
    return !isLetter.test(before) && !isLetter.test(after);
  };

  const ranges: { start: number; end: number; key: string }[] = [];
  for (const c of cands) {
    const positions: number[] = [];
    let from = 0;
    let idx: number;
    while ((idx = text.indexOf(c.surname, from)) !== -1) {
      if (onBoundary(idx, idx + c.surname.length)) positions.push(idx);
      from = idx + c.surname.length;
    }
    if (!positions.length) continue;
    let chosen = -1;
    if (c.year) {
      for (const pos of positions) {
        const end = pos + c.surname.length;
        if (!overlaps(pos, end) && text.slice(pos, end + 80).includes(c.year)) {
          chosen = pos;
          break;
        }
      }
    }
    if (chosen === -1) {
      for (const pos of positions) {
        if (!overlaps(pos, pos + c.surname.length)) {
          chosen = pos;
          break;
        }
      }
    }
    if (chosen === -1) continue;
    const end = chosen + c.surname.length;
    ranges.push({ start: chosen, end, key: c.key });
    claimed.push([chosen, end]);
  }

  ranges.sort((a, b) => a.start - b.start);
  let out = "";
  let cursor = 0;
  for (const r of ranges) {
    if (r.start < cursor) continue;
    out += text.slice(cursor, r.start);
    out += `<a href="#/references#${r.key}" class="ref-cite">${text.slice(
      r.start,
      r.end,
    )}</a>`;
    cursor = r.end;
  }
  out += text.slice(cursor);
  return out;
}
