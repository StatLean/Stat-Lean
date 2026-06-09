import { useMemo } from "react";
import { useParams, Link, Navigate } from "react-router-dom";
import { getResult } from "../lib/data";
import { renderLean } from "../lib/render";
import { docUrl, sourceUrl } from "../lib/site";
import { MathText } from "../components/MathText";
import { DepGraph } from "../components/DepGraph";

export function GraphView() {
  const { resultId } = useParams<{ resultId: string }>();
  const r = resultId ? getResult(resultId) : undefined;
  const leanHtml = useMemo(
    () => (r ? renderLean(r.leanSignature, r.hypotheses) : ""),
    [r],
  );
  if (!r) return <Navigate to="/" replace />;

  return (
    <div data-cat={r.category} className="h-[calc(100vh-4rem)] flex flex-col">
      {/* slim header bar */}
      <div className="shrink-0 border-b hairline px-5 sm:px-7 py-3 flex items-center gap-x-4 gap-y-1 flex-wrap">
        <Link
          to={`/result/${r.id}`}
          className="font-sans text-sm text-ink-soft hover:text-ink shrink-0"
        >
          ← Back to result
        </Link>
        <span className="hidden sm:inline text-rule">|</span>
        <span className="text-[0.62rem] font-sans font-semibold uppercase tracking-widest px-2 py-0.5 rounded-full bg-accent/15 accent shrink-0">
          {r.kind}
        </span>
        <h1 className="font-display text-lg font-semibold truncate min-w-0">
          {r.title}
        </h1>
        <div className="ml-auto flex items-center gap-2 font-sans text-xs shrink-0">
          <a href={docUrl(r)} className="btn-action">↗ doc-gen4</a>
          <a href={sourceUrl(r)} className="btn-action">⟨⟩ source</a>
        </div>
      </div>

      {/* main: graph + statements sidebar */}
      <div className="flex-1 flex min-h-0">
        <div className="flex-1 min-w-0 p-4 flex flex-col">
          <h2 className="font-sans text-xs uppercase tracking-widest text-ink-faint mb-2 shrink-0">
            Dependency graph · rooted at{" "}
            <code className="font-mono accent normal-case tracking-normal">{r.leanName}</code>,
            expanded to first-level Mathlib results
          </h2>
          <div className="flex-1 min-h-0">
            <DepGraph id={r.id} fill />
          </div>
        </div>

        <aside className="hidden md:flex flex-col w-[340px] xl:w-[400px] shrink-0 border-l hairline overflow-y-auto">
          <div className="p-5 border-b hairline">
            <div className="font-sans text-xs uppercase tracking-widest text-ink-faint mb-2">
              Informal statement · {r.citation}
            </div>
            <MathText
              html={r.informal}
              className="informal-body font-serif text-[0.95rem] leading-relaxed text-ink"
            />
          </div>
          <div className="p-5 bg-parchment-sunk/40">
            <div className="font-sans text-xs uppercase tracking-widest text-ink-faint mb-2">
              Lean formalization
            </div>
            <div className="overflow-x-auto lean-scroll">
              <pre className="lean-code">
                <code dangerouslySetInnerHTML={{ __html: leanHtml }} />
              </pre>
            </div>
            {r.formalizationNotes && (
              <p className="mt-4 font-serif text-sm text-ink-soft leading-relaxed border-l-2 border-accent pl-3">
                {r.formalizationNotes}
              </p>
            )}
          </div>
        </aside>
      </div>
    </div>
  );
}
