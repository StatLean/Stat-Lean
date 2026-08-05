import { useMemo, useState } from "react";
import { Link } from "react-router-dom";
import { RESULTS } from "../lib/data";
import { CATEGORY_BY_ID } from "../lib/categories";
import type { ResultEntry } from "../lib/types";

/**
 * Subject index, in the style of a mathematics textbook's back matter: terms in
 * one alphabetical sequence, and where several terms share a leading word the
 * word is printed once as a head and the remainders are indented beneath it
 * (van der Vaart, *Asymptotic Statistics*, pp. 435-443). Each term expands to
 * the results carrying it.
 */

interface Term {
  /** the full index term, e.g. "convergence in distribution" */
  term: string;
  results: ResultEntry[];
}

interface Group {
  /** shared leading word, when the group has more than one term */
  head: string;
  terms: Term[];
}

const collator = new Intl.Collator("en", { sensitivity: "base", numeric: true });

/** Leading word of a term, used to build the indented sub-entry groups. */
function headWord(term: string): string {
  return term.split(/\s+/)[0]!.toLowerCase().replace(/[.,;:]$/, "");
}

/** First letter used for the A-Z rail; everything non-alphabetic files under "#". */
function initial(term: string): string {
  const c = term.trim()[0]?.toUpperCase() ?? "#";
  return c >= "A" && c <= "Z" ? c : "#";
}

export default function IndexPage() {
  const [open, setOpen] = useState<Set<string>>(new Set());
  const [query, setQuery] = useState("");

  const toggle = (t: string) =>
    setOpen((prev) => {
      const next = new Set(prev);
      next.has(t) ? next.delete(t) : next.add(t);
      return next;
    });

  const groups = useMemo<Group[]>(() => {
    const byTerm = new Map<string, ResultEntry[]>();
    for (const r of RESULTS) {
      for (const raw of r.keywords ?? []) {
        const term = raw.trim();
        if (!term) continue;
        const list = byTerm.get(term) ?? [];
        list.push(r);
        byTerm.set(term, list);
      }
    }

    const q = query.trim().toLowerCase();
    let terms: Term[] = [...byTerm.entries()]
      .map(([term, results]) => ({
        term,
        results: [...results].sort((a, b) => collator.compare(a.title, b.title)),
      }))
      .sort((a, b) => collator.compare(a.term, b.term));

    if (q) terms = terms.filter((t) => t.term.toLowerCase().includes(q));

    // Collapse runs of terms sharing a leading word into one indented group.
    const out: Group[] = [];
    for (const t of terms) {
      const head = headWord(t.term);
      const last = out.length > 0 ? out[out.length - 1] : undefined;
      if (last && headWord(last.terms[0]!.term) === head) last.terms.push(t);
      else out.push({ head, terms: [t] });
    }
    return out;
  }, [query]);

  const totalTerms = groups.reduce((n, g) => n + g.terms.length, 0);
  const letters = useMemo(() => {
    const seen = new Set<string>();
    for (const g of groups) seen.add(initial(g.terms[0]!.term));
    return [...seen].sort();
  }, [groups]);

  /** Sub-entry text: the remainder after the shared head word. */
  const remainder = (term: string) =>
    term.slice(term.split(/\s+/)[0]!.length).trim();

  const renderResults = (t: Term) => (
    <ul className="mt-2 ml-1 space-y-1.5 border-l hairline pl-4">
      {t.results.map((r) => (
        <li key={r.id} className="leading-snug">
          <Link
            to={`/result/${r.id}`}
            data-cat={r.category}
            className="ulink font-serif text-[0.98rem] text-ink hover:accent"
          >
            {r.title}
          </Link>
          <span className="ml-2 font-sans text-xs text-ink-faint">
            {CATEGORY_BY_ID[r.category]?.name ?? r.category}
          </span>
        </li>
      ))}
    </ul>
  );

  const termRow = (t: Term, indented: boolean) => {
    const isOpen = open.has(t.term);
    const label = indented ? remainder(t.term) : t.term;
    return (
      <li key={t.term} className={indented ? "ml-6" : ""}>
        <button
          type="button"
          onClick={() => toggle(t.term)}
          aria-expanded={isOpen}
          className="w-full flex items-baseline gap-2 py-1 text-left group"
        >
          <span className="font-serif text-[1.02rem] text-ink group-hover:accent transition-colors">
            {label}
          </span>
          <span className="flex-1 border-b border-dotted hairline translate-y-[-0.25rem]" />
          <span className="shrink-0 font-sans text-xs text-ink-faint">
            {t.results.length}
          </span>
          <span
            className={`shrink-0 font-sans text-xs text-ink-faint transition-transform ${
              isOpen ? "rotate-90" : ""
            }`}
          >
            ▸
          </span>
        </button>
        {isOpen && renderResults(t)}
      </li>
    );
  };

  return (
    <main>
      <section className="border-b hairline">
        <div className="max-w-page mx-auto px-5 sm:px-8 pt-16 pb-10">
          <h1 className="font-display text-4xl sm:text-5xl font-semibold tracking-tight">
            Index
          </h1>
          <p className="mt-4 font-serif text-ink-soft max-w-3xl leading-relaxed">
            Subject index of the formalized theory. {totalTerms} terms across{" "}
            {RESULTS.length} results; select a term to list the results that
            carry it. Terms sharing a leading word are grouped, as in a
            textbook's back matter.
          </p>
          <input
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="Filter terms…"
            aria-label="Filter index terms"
            className="mt-6 w-full max-w-md rounded-full border hairline bg-parchment-panel px-5 py-2.5 font-sans text-sm outline-none focus:border-accent/60"
          />
          {letters.length > 1 && (
            <nav className="mt-5 flex flex-wrap gap-x-3 gap-y-1" aria-label="Jump to letter">
              {letters.map((l) => (
                <a
                  key={l}
                  href={`#idx-${l}`}
                  className="font-sans text-sm text-ink-faint hover:accent transition-colors"
                >
                  {l}
                </a>
              ))}
            </nav>
          )}
        </div>
      </section>

      <section className="max-w-page mx-auto px-5 sm:px-8 py-10">
        {groups.length === 0 ? (
          <p className="font-serif text-ink-soft">No terms match that filter.</p>
        ) : (
          <ol className="columns-1 lg:columns-2 gap-x-14">
            {groups.map((g, gi) => {
              const first = g.terms[0]!;
              const letter = initial(first.term);
              const isFirstOfLetter =
                gi === 0 || initial(groups[gi - 1]!.terms[0]!.term) !== letter;
              return (
                <li
                  key={g.head + gi}
                  className="break-inside-avoid mb-3"
                  id={isFirstOfLetter ? `idx-${letter}` : undefined}
                >
                  {isFirstOfLetter && (
                    <h2 className="scroll-mt-24 mt-6 mb-2 font-display text-xl font-semibold accent">
                      {letter}
                    </h2>
                  )}
                  {g.terms.length === 1 ? (
                    <ul>{termRow(first, false)}</ul>
                  ) : (
                    <>
                      <p className="font-serif text-[1.02rem] text-ink">{g.head}</p>
                      <ul>{g.terms.map((t) => termRow(t, true))}</ul>
                    </>
                  )}
                </li>
              );
            })}
          </ol>
        )}
      </section>
    </main>
  );
}
