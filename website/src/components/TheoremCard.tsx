import { Link } from "react-router-dom";
import type { ResultEntry } from "../lib/types";

const KIND_LABEL: Record<string, string> = {
  definition: "Def",
  theorem: "Thm",
  lemma: "Lem",
  proposition: "Prop",
  corollary: "Cor",
  equation: "Eq",
};

export function TheoremCard({ r, index = 0 }: { r: ResultEntry; index?: number }) {
  return (
    <Link
      to={`/result/${r.id}`}
      data-cat={r.category}
      className="group relative block rounded-xl border hairline bg-parchment-panel p-5 transition-all duration-300 hover:-translate-y-0.5 hover:border-accent/50 hover:shadow-[0_8px_30px_-12px_rgb(var(--accent)/0.35)]"
      style={{ animationDelay: `${Math.min(index, 12) * 40}ms` }}
    >
      <div className="flex items-center gap-2 mb-2.5">
        <span className="text-[0.62rem] font-sans font-semibold uppercase tracking-widest accent">
          {KIND_LABEL[r.kind] ?? r.kind}
        </span>
      </div>

      <h3 className="font-display text-[1.07rem] font-semibold leading-snug text-ink group-hover:accent transition-colors">
        {r.title}
      </h3>

      <p className="mt-1.5 text-sm text-ink-soft font-serif leading-relaxed line-clamp-3">
        {r.summary}
      </p>

      <code className="mt-3 inline-block max-w-full truncate text-[0.72rem] font-mono text-ink-faint group-hover:text-ink-soft transition-colors">
        {r.leanName}
      </code>

      <span className="pointer-events-none absolute right-4 top-4 text-ink-faint opacity-0 group-hover:opacity-100 transition-opacity">
        →
      </span>
    </Link>
  );
}
