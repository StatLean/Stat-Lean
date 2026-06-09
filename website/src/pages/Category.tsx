import { useMemo, useState } from "react";
import { useParams, Link, Navigate } from "react-router-dom";
import { CATEGORY_BY_ID } from "../lib/categories";
import { resultsByCategory } from "../lib/data";
import type { CategoryId, ResultKind } from "../lib/types";
import { TheoremCard } from "../components/TheoremCard";
import { ConvergenceMark } from "../components/ConvergenceMark";

const KIND_ORDER: ResultKind[] = [
  "definition",
  "theorem",
  "lemma",
  "proposition",
  "corollary",
  "equation",
];

export function Category() {
  const { catId } = useParams<{ catId: CategoryId }>();
  const meta = catId ? CATEGORY_BY_ID[catId] : undefined;
  const [query, setQuery] = useState("");
  const [kind, setKind] = useState<ResultKind | "all">("all");

  const all = useMemo(
    () => (catId ? resultsByCategory(catId) : []),
    [catId],
  );

  const kinds = useMemo(() => {
    const present = new Set(all.map((r) => r.kind));
    return KIND_ORDER.filter((k) => present.has(k));
  }, [all]);

  const filtered = useMemo(() => {
    const q = query.trim().toLowerCase();
    return all.filter((r) => {
      if (kind !== "all" && r.kind !== kind) return false;
      if (!q) return true;
      return (
        r.title.toLowerCase().includes(q) ||
        r.summary.toLowerCase().includes(q) ||
        r.leanName.toLowerCase().includes(q) ||
        r.citation.toLowerCase().includes(q)
      );
    });
  }, [all, query, kind]);

  if (!meta) return <Navigate to="/" replace />;

  return (
    <div data-cat={meta.id}>
      {/* category header */}
      <section className="relative overflow-hidden border-b hairline">
        <ConvergenceMark
          rings={7}
          className="pointer-events-none absolute -right-16 -top-20 w-96 h-96 accent opacity-[0.09]"
        />
        <div className="max-w-page mx-auto px-5 sm:px-8 py-14 relative">
          <div className="flex items-center gap-2 text-sm font-sans text-ink-faint mb-4">
            <Link to="/" className="ulink">Topics</Link>
            <span>/</span>
            <span className="accent">{meta.name}</span>
          </div>
          <h1 className="font-display text-4xl sm:text-5xl font-semibold tracking-tight">
            {meta.name}
          </h1>
          <p className="mt-2 font-sans accent">{meta.tagline}</p>
          <p className="mt-4 max-w-2xl font-serif text-lg text-ink-soft leading-relaxed">
            {meta.blurb}
          </p>
        </div>
      </section>

      {/* controls */}
      <div className="sticky top-16 z-30 bg-parchment/85 backdrop-blur-md border-b hairline">
        <div className="max-w-page mx-auto px-5 sm:px-8 py-3 flex flex-wrap items-center gap-3">
          <input
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="Search this topic…"
            className="flex-1 min-w-[12rem] bg-parchment-sunk border hairline rounded-full px-4 py-2 text-sm font-sans outline-none focus:border-accent/60 transition-colors"
          />
          <div className="flex items-center gap-1.5 flex-wrap font-sans text-xs">
            <FilterChip active={kind === "all"} onClick={() => setKind("all")}>
              All
            </FilterChip>
            {kinds.map((k) => (
              <FilterChip key={k} active={kind === k} onClick={() => setKind(k)}>
                {k[0].toUpperCase() + k.slice(1)}
              </FilterChip>
            ))}
          </div>
          <span className="ml-auto text-xs font-sans text-ink-faint">
            {filtered.length} / {all.length}
          </span>
        </div>
      </div>

      {/* grid */}
      <section className="max-w-page mx-auto px-5 sm:px-8 py-10">
        {filtered.length === 0 ? (
          <p className="font-serif text-ink-soft py-16 text-center">
            No results match “{query}”.
          </p>
        ) : (
          <div className="grid gap-4 sm:grid-cols-2 lg:grid-cols-3">
            {filtered.map((r, i) => (
              <div key={r.id} className="animate-rise">
                <TheoremCard r={r} index={i} />
              </div>
            ))}
          </div>
        )}
      </section>
    </div>
  );
}

function FilterChip({
  active,
  onClick,
  children,
}: {
  active: boolean;
  onClick: () => void;
  children: React.ReactNode;
}) {
  return (
    <button
      onClick={onClick}
      className={`px-3 py-1.5 rounded-full transition-colors ${
        active
          ? "bg-accent/15 accent font-medium"
          : "text-ink-soft hover:text-ink border hairline"
      }`}
    >
      {children}
    </button>
  );
}
