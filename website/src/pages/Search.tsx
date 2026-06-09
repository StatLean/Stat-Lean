import { useMemo, useState } from "react";
import { RESULTS } from "../lib/data";
import { CATEGORIES } from "../lib/categories";
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

export function Search() {
  const [query, setQuery] = useState("");
  const [kind, setKind] = useState<ResultKind | "all">("all");
  const [topic, setTopic] = useState<CategoryId | "all">("all");

  const kinds = useMemo(() => {
    const present = new Set(RESULTS.map((r) => r.kind));
    return KIND_ORDER.filter((k) => present.has(k));
  }, []);

  const filtered = useMemo(() => {
    const q = query.trim().toLowerCase();
    return RESULTS.filter((r) => {
      if (topic !== "all" && r.category !== topic) return false;
      if (kind !== "all" && r.kind !== kind) return false;
      if (!q) return true;
      return (
        r.title.toLowerCase().includes(q) ||
        r.summary.toLowerCase().includes(q) ||
        r.leanName.toLowerCase().includes(q)
      );
    });
  }, [query, kind, topic]);

  return (
    <div data-cat={topic === "all" ? undefined : topic}>
      <section className="relative overflow-hidden border-b hairline">
        <ConvergenceMark
          rings={7}
          className="pointer-events-none absolute -right-16 -top-20 w-96 h-96 text-ink opacity-[0.06]"
        />
        <div className="max-w-page mx-auto px-5 sm:px-8 py-12 relative">
          <h1 className="font-display text-4xl sm:text-5xl font-semibold tracking-tight">
            Search
          </h1>
          <p className="mt-3 max-w-2xl font-serif text-lg text-ink-soft leading-relaxed">
            All {RESULTS.length} formalized results. Filter by topic and kind, or
            search by name.
          </p>
        </div>
      </section>

      {/* controls */}
      <div className="sticky top-16 z-30 bg-parchment/85 backdrop-blur-md border-b hairline">
        <div className="max-w-page mx-auto px-5 sm:px-8 py-3 space-y-2">
          <div className="flex flex-wrap items-center gap-3">
            <input
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Search results…"
              autoFocus
              className="flex-1 min-w-[12rem] bg-parchment-sunk border hairline rounded-full px-4 py-2 text-sm font-sans outline-none focus:border-ink/40 transition-colors"
            />
            <span className="text-xs font-sans text-ink-faint">
              {filtered.length} / {RESULTS.length}
            </span>
          </div>
          <div className="flex flex-wrap items-center gap-x-4 gap-y-2 font-sans text-xs">
            <div className="flex items-center gap-1.5 flex-wrap">
              <span className="text-ink-faint uppercase tracking-widest mr-1">Topic</span>
              <Chip active={topic === "all"} onClick={() => setTopic("all")}>All</Chip>
              {CATEGORIES.map((c) => (
                <Chip
                  key={c.id}
                  active={topic === c.id}
                  data-cat={c.id}
                  onClick={() => setTopic(c.id)}
                >
                  {c.name.replace(" Statistics", "").replace(" Results", "")}
                </Chip>
              ))}
            </div>
            <div className="flex items-center gap-1.5 flex-wrap">
              <span className="text-ink-faint uppercase tracking-widest mr-1">Kind</span>
              <Chip active={kind === "all"} onClick={() => setKind("all")}>All</Chip>
              {kinds.map((k) => (
                <Chip key={k} active={kind === k} onClick={() => setKind(k)}>
                  {k[0].toUpperCase() + k.slice(1)}
                </Chip>
              ))}
            </div>
          </div>
        </div>
      </div>

      <section className="max-w-page mx-auto px-5 sm:px-8 py-10">
        {filtered.length === 0 ? (
          <p className="font-serif text-ink-soft py-16 text-center">
            No results match your filters.
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

function Chip({
  active,
  onClick,
  children,
  ...rest
}: {
  active: boolean;
  onClick: () => void;
  children: React.ReactNode;
} & React.HTMLAttributes<HTMLButtonElement>) {
  return (
    <button
      onClick={onClick}
      {...rest}
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
