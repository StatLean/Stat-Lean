import { useEffect, useMemo, useRef } from "react";
import { useLocation } from "react-router-dom";
import { ConvergenceMark } from "../components/ConvergenceMark";
import { MathText } from "../components/MathText";
import type { Reference } from "../lib/types";
import rawRefs from "../data/references.json";

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

export function References() {
  const { hash } = useLocation();
  const containerRef = useRef<HTMLDivElement>(null);

  const ordered = useMemo(
    () =>
      [...REFERENCES].sort((a, b) => {
        const t = sortToken(a.sortKey).localeCompare(sortToken(b.sortKey));
        return t !== 0 ? t : a.key.localeCompare(b.key);
      }),
    [],
  );

  // Scroll to (and briefly highlight) the targeted reference: #/references#<key>.
  useEffect(() => {
    const id = hash.replace(/^#/, "");
    if (!id) return;
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
            alphabetically by author. Each result page links to the relevant
            entry here.
          </p>
        </div>
      </section>

      <section className="max-w-page mx-auto px-5 sm:px-8 py-10">
        <ol className="space-y-3">
          {ordered.map((r) => (
            <li
              key={r.key}
              id={r.key}
              className="ref-item scroll-mt-24 rounded-xl border hairline bg-parchment-panel px-5 py-4 transition-colors"
            >
              <MathText
                html={r.html}
                markdown
                className="font-serif text-[1.02rem] leading-relaxed text-ink"
              />
            </li>
          ))}
        </ol>
      </section>
    </div>
  );
}
