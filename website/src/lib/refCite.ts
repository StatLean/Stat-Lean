import type { Reference } from "./types";
import rawRefs from "../data/references.json";

const REF_BY_KEY = new Map((rawRefs as unknown as Reference[]).map((r) => [r.key, r]));

export interface ReferenceLink {
  key: string;
  label: string;
}

/**
 * Return a stable, human-readable link label for every source attached to a
 * result.  Inline author matching is necessarily heuristic; this list is the
 * reliable fallback that makes every cited source reachable from the comment.
 */
export function referenceLinks(keys: string[]): ReferenceLink[] {
  return (keys ?? []).flatMap((key) => {
    const ref = REF_BY_KEY.get(key);
    if (!ref) return [];
    const year = key.match(/(?:18|19|20)\d{2}/)?.[0]
      ?? ref.html.match(/(?:18|19|20)\d{2}/)?.[0];
    return [{ key, label: `${ref.sortKey}${year ? ` (${year})` : ""}` }];
  });
}

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
      // A year-bearing key only links where ITS OWN year appears nearby (so the
      // 1991 "van der Vaart" paper doesn't get linked to the 1998 textbook, and
      // an uncited key doesn't grab a stray mention of its author).
      const yre = new RegExp(`\\b${c.year}\\b`);
      for (const pos of positions) {
        const e = pos + c.surname.length;
        if (!overlaps(pos, e) && yre.test(text.slice(e, e + 400))) {
          chosen = pos;
          break;
        }
      }
    } else {
      for (const pos of positions) {
        if (!overlaps(pos, pos + c.surname.length)) {
          chosen = pos;
          break;
        }
      }
    }
    if (chosen === -1) continue;
    const sEnd = chosen + c.surname.length;

    // Extend the span to cover the whole inline citation, not just the surname:
    //  - left over author initials ("W. ", "L. ", "J.-B. ")
    //  - right through the key's year and an optional trailing page range.
    let start = chosen;
    const pre = text.slice(Math.max(0, chosen - 16), chosen);
    const im = pre.match(/(?:\p{Lu}\.[-\s]*)+\s*$/u);
    if (im) start = chosen - im[0].length;

    let end = sEnd;
    if (c.year) {
      const yi = text.slice(sEnd, sEnd + 400).indexOf(c.year);
      if (yi !== -1) {
        end = sEnd + yi + c.year.length;
        const tail = text
          .slice(end, end + 48)
          .match(/^\s*,?\s*(?:pp?\.\s*)?\p{Nd}+\s*[–-]\s*\p{Nd}+/u);
        if (tail) end += tail[0].length;
        // close a parenthesis the span opened (e.g. "… Review 59 (1991" → "…(1991)")
        const span = text.slice(start, end);
        const opens = (span.match(/\(/g) ?? []).length;
        const closes = (span.match(/\)/g) ?? []).length;
        if (opens > closes && text[end] === ")") end += 1;
      }
    }

    if (overlaps(start, end)) continue;
    ranges.push({ start, end, key: c.key });
    claimed.push([start, end]);
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
