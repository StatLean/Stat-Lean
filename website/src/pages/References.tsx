import { useEffect, useMemo, useRef, useState } from "react";
import { Link, useLocation } from "react-router-dom";
import { ConvergenceMark } from "../components/ConvergenceMark";
import { MathText } from "../components/MathText";
import type { Reference } from "../lib/types";
import rawRefs from "../data/references.json";
import { REF_INDEX, citingCount, type Citing } from "../lib/refIndex";
import { isTextbook, chapterWord, chapterTitle } from "../lib/bookChapters";

const REFERENCES = rawRefs as unknown as Reference[];

/** Normalize a surname for ordering: drop accents, lowercase, ignore particles. */
function sortToken(s: string): string {
  return s
    .normalize("NFD")
    .replace(/[̀-ͯ]/g, "")
    .toLowerCase()
    .replace(/^(van der|van|von|de|del|la)\s+/, "")
    .trim();
}

/** Group primary cites by chapter, ascending; unparsed chapters last. */
function byChapter(items: Citing[]): { chapter: number | null; items: Citing[] }[] {
  const map = new Map<number | null, Citing[]>();
  for (const c of items) {
    const arr = map.get(c.chapter) ?? [];
    arr.push(c);
    map.set(c.chapter, arr);
  }
  const groups = [...map.entries()].map(([chapter, its]) => ({
    chapter,
    items: its.sort((a, b) => a.order - b.order || a.title.localeCompare(b.title)),
  }));
  groups.sort((a, b) => {
    if (a.chapter == null) return 1;
    if (b.chapter == null) return -1;
    return a.chapter - b.chapter;
  });
  return groups;
}

function ResultLink({ c, showItem }: { c: Citing; showItem?: boolean }) {
  return (
    <Link
      to={`/result/${c.id}`}
      data-cat={c.category}
      className="group flex gap-2 rounded-lg px-2 py-1.5 -mx-2 hover:bg-accent/[0.07] transition-colors"
    >
      {showItem && (
        <span className="font-mono text-xs accent shrink-0 pt-0.5 min-w-[4.5rem]">
          {c.itemLabel}
        </span>
      )}
      <span className="font-serif text-[0.97rem] text-ink-soft group-hover:text-ink leading-snug">
        {c.title}
      </span>
    </Link>
  );
}

function ExpandedBody({ refKey }: { refKey: string }) {
  const citing = REF_INDEX.get(refKey) ?? [];
  if (!isTextbook(refKey)) {
    const items = [...citing].sort(
      (a, b) => a.order - b.order || a.title.localeCompare(b.title),
    );
    return (
      <div className="grid sm:grid-cols-2 gap-x-6">
        {items.map((c) => (
          <ResultLink key={c.id} c={c} />
        ))}
      </div>
    );
  }
  const word = chapterWord(refKey);
  const primary = citing.filter((c) => c.isPrimary);
  const secondary = citing.filter((c) => !c.isPrimary);
  const groups = byChapter(primary);
  return (
    <div className="space-y-4">
      {groups.map((g) => (
        <div key={String(g.chapter)}>
          <h4 className="font-sans text-xs uppercase tracking-widest text-ink-faint mb-1.5">
            {g.chapter == null
              ? "Other"
              : `${word} ${g.chapter}${
                  chapterTitle(refKey, g.chapter)
                    ? " — " + chapterTitle(refKey, g.chapter)
                    : ""
                }`}
          </h4>
          <div className="pl-1">
            {g.items.map((c) => (
              <ResultLink key={c.id} c={c} showItem />
            ))}
          </div>
        </div>
      ))}
      {secondary.length > 0 && (
        <div>
          <h4 className="font-sans text-xs uppercase tracking-widest text-ink-faint mb-1.5">
            Also cited in bibliographic comments
          </h4>
          <div className="grid sm:grid-cols-2 gap-x-6 pl-1">
            {secondary
              .sort((a, b) => a.title.localeCompare(b.title))
              .map((c) => (
                <ResultLink key={c.id} c={c} />
              ))}
          </div>
        </div>
      )}
    </div>
  );
}

export function References() {
  const { hash } = useLocation();
  const containerRef = useRef<HTMLDivElement>(null);
  const [open, setOpen] = useState<Set<string>>(new Set());

  const ordered = useMemo(
    () =>
      [...REFERENCES].sort((a, b) => {
        const t = sortToken(a.sortKey).localeCompare(sortToken(b.sortKey));
        return t !== 0 ? t : a.key.localeCompare(b.key);
      }),
    [],
  );

  const toggle = (key: string) =>
    setOpen((prev) => {
      const next = new Set(prev);
      next.has(key) ? next.delete(key) : next.add(key);
      return next;
    });

  // Deep link #/references#<key>: scroll to, highlight, and auto-expand.
  useEffect(() => {
    const id = hash.replace(/^#/, "");
    if (!id) return;
    setOpen((prev) => (prev.has(id) ? prev : new Set(prev).add(id)));
    const el = containerRef.current?.querySelector<HTMLElement>(
      `[id="${CSS.escape(id)}"]`,
    );
    if (!el) return;
    el.scrollIntoView({ behavior: "smooth", block: "center" });
    el.classList.add("ref-flash");
    const t = setTimeout(() => el.classList.remove("ref-flash"), 1600);
    return () => clearTimeout(t);
  }, [hash, ordered]);

  return (
    <div ref={containerRef}>
      <section className="relative overflow-hidden border-b hairline">
        <ConvergenceMark
          rings={6}
          className="pointer-events-none absolute -right-12 -top-16 w-72 h-72 text-ink opacity-[0.05]"
        />
        <div className="max-w-page mx-auto px-5 sm:px-8 py-12 relative">
          <p className="font-sans text-xs uppercase tracking-[0.3em] text-ink-faint mb-4">
            Bibliography
          </p>
          <h1 className="font-display text-4xl sm:text-5xl font-semibold tracking-tight">
            References
          </h1>
          <p className="mt-4 font-serif text-ink-soft max-w-2xl leading-relaxed">
            The textbooks and papers cited across the library, ordered
            alphabetically by author. Expand any entry to see the results that
            cite it — textbooks are organized by chapter.
          </p>
        </div>
      </section>

      <section className="max-w-page mx-auto px-5 sm:px-8 py-10">
        <ol className="space-y-3">
          {ordered.map((r) => {
            const n = citingCount(r.key);
            const isOpen = open.has(r.key);
            return (
              <li
                key={r.key}
                id={r.key}
                className="ref-item scroll-mt-24 rounded-xl border hairline bg-parchment-panel transition-colors"
              >
                <button
                  type="button"
                  onClick={() => n > 0 && toggle(r.key)}
                  aria-expanded={isOpen}
                  className={`w-full flex items-start gap-3 px-5 py-4 text-left ${
                    n > 0 ? "cursor-pointer" : "cursor-default"
                  }`}
                >
                  <MathText
                    html={r.html}
                    markdown
                    className="flex-1 font-serif text-[1.02rem] leading-relaxed text-ink"
                  />
                  {n > 0 && (
                    <span className="shrink-0 flex items-center gap-1.5 font-sans text-xs text-ink-faint pt-1">
                      {n} result{n === 1 ? "" : "s"}
                      <span
                        className={`inline-block transition-transform ${
                          isOpen ? "rotate-90" : ""
                        }`}
                      >
                        ▸
                      </span>
                    </span>
                  )}
                </button>
                {isOpen && n > 0 && (
                  <div className="px-5 pb-5 pt-1 border-t hairline">
                    <ExpandedBody refKey={r.key} />
                  </div>
                )}
              </li>
            );
          })}
        </ol>
      </section>
    </div>
  );
}
