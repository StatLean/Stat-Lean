import { useEffect, useMemo, useRef } from "react";
import { useParams, Link, Navigate } from "react-router-dom";
import { getResult, resultsByCategory } from "../lib/data";
import { CATEGORY_BY_ID } from "../lib/categories";
import { renderLean } from "../lib/render";
import { docUrl, sourceUrl } from "../lib/site";
import { MathText } from "../components/MathText";
import { ConvergenceMark } from "../components/ConvergenceMark";
import { Logo } from "../components/Logo";

export function ResultDetail() {
  const { resultId } = useParams<{ resultId: string }>();
  const r = resultId ? getResult(resultId) : undefined;
  const containerRef = useRef<HTMLDivElement>(null);

  const leanHtml = useMemo(
    () => (r ? renderLean(r.leanSignature, r.hypotheses) : ""),
    [r],
  );

  // bidirectional hover highlighting between informal spans and Lean tokens
  useEffect(() => {
    const root = containerRef.current;
    if (!root || !r) return;
    const nodes = Array.from(root.querySelectorAll<HTMLElement>("[data-link]"));
    const byId = new Map<string, HTMLElement[]>();
    for (const n of nodes) {
      const id = n.dataset.link!;
      (byId.get(id) ?? byId.set(id, []).get(id)!).push(n);
    }
    const setActive = (id: string, on: boolean) =>
      byId.get(id)?.forEach((n) => n.classList.toggle("hl-active", on));

    const onOver = (e: Event) => {
      const t = (e.target as HTMLElement).closest<HTMLElement>("[data-link]");
      if (t) setActive(t.dataset.link!, true);
    };
    const onOut = (e: Event) => {
      const t = (e.target as HTMLElement).closest<HTMLElement>("[data-link]");
      if (t) setActive(t.dataset.link!, false);
    };
    root.addEventListener("mouseover", onOver);
    root.addEventListener("mouseout", onOut);
    return () => {
      root.removeEventListener("mouseover", onOver);
      root.removeEventListener("mouseout", onOut);
    };
  }, [r, leanHtml]);

  if (!r) return <Navigate to="/" replace />;
  const meta = CATEGORY_BY_ID[r.category];

  const siblings = resultsByCategory(r.category);
  const idx = siblings.findIndex((s) => s.id === r.id);
  const prev = siblings[idx - 1];
  const next = siblings[idx + 1];

  return (
    <div data-cat={r.category} ref={containerRef}>
      {/* header */}
      <section className="relative overflow-hidden border-b hairline">
        <ConvergenceMark
          rings={6}
          className="pointer-events-none absolute -right-12 -top-16 w-72 h-72 accent opacity-[0.08]"
        />
        <div className="max-w-page mx-auto px-5 sm:px-8 py-10 relative flex items-center gap-12">
          <div className="flex-1 min-w-0">
            <div className="flex items-center gap-2 text-sm font-sans text-ink-faint mb-4 flex-wrap">
              <Link to="/" className="ulink">Topics</Link>
              <span>/</span>
              <Link to={`/category/${r.category}`} className="ulink accent">
                {meta.name}
              </Link>
            </div>

            <div className="flex items-center gap-3 mb-3">
              <span className="text-[0.65rem] font-sans font-semibold uppercase tracking-[0.2em] px-2.5 py-1 rounded-full bg-accent/15 accent">
                {r.kind}
              </span>
            </div>

            <h1 className="font-display text-3xl sm:text-4xl font-semibold tracking-tight max-w-4xl">
              {r.title}
            </h1>

            <div className="mt-5 flex flex-wrap gap-2.5 font-sans text-sm">
              <a href={docUrl(r)} className="btn-action">
                <span>↗</span> doc-gen4 reference
              </a>
              <a href={sourceUrl(r)} className="btn-action">
                <span>⟨⟩</span> Lean source
              </a>
              <Link to={`/result/${r.id}/graph`} className="btn-action border-accent/50 accent">
                <span>◈</span> Show dependency graph
              </Link>
            </div>
          </div>
          <Logo className="hidden lg:block shrink-0 w-32 h-32 text-ink opacity-75" />
        </div>
      </section>

      {/* aligned panes */}
      <section className="max-w-page mx-auto px-5 sm:px-8 py-10">
        <div className="grid gap-6 lg:grid-cols-2 items-start">
          {/* informal */}
          <div className="rounded-2xl border hairline bg-parchment-panel overflow-hidden">
            <PaneHeader label="Informal statement" sub={r.citation} />
            <div className="p-6">
              <MathText
                html={r.informal}
                className="informal-body font-serif text-[1.05rem] leading-relaxed text-ink space-y-3 [&_.hl-span]:[--x:0]"
              />
            </div>
          </div>

          {/* lean */}
          <div className="rounded-2xl border hairline bg-parchment-sunk overflow-hidden">
            <PaneHeader
              label="Lean 4 formalization"
              sub={r.fullName}
              mono
            />
            <div className="p-5 overflow-x-auto lean-scroll">
              <pre className="lean-code">
                <code dangerouslySetInnerHTML={{ __html: leanHtml }} />
              </pre>
            </div>
          </div>
        </div>

        {/* hypothesis legend */}
        {r.hypotheses.length > 0 && (
          <div className="mt-6 rounded-2xl border hairline bg-parchment-panel p-6">
            <h3 className="font-sans text-xs uppercase tracking-widest text-ink-faint mb-4">
              Hypothesis correspondence · hover to cross-highlight
            </h3>
            <div className="grid gap-3 sm:grid-cols-2">
              {r.hypotheses.map((h) => (
                <div
                  key={h.id}
                  data-link={h.id}
                  className="hl-token flex gap-3 rounded-lg px-3 py-2 -mx-1 cursor-help"
                >
                  <code className="font-mono text-xs accent shrink-0 pt-0.5 max-w-[40%] truncate">
                    {h.leanToken}
                  </code>
                  <div className="min-w-0">
                    <div className="font-sans text-sm font-medium">{h.label}</div>
                    {h.note && (
                      <div className="font-serif text-sm text-ink-soft leading-snug">
                        {h.note}
                      </div>
                    )}
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* formalization notes */}
        {r.formalizationNotes && (
          <div className="mt-6 rounded-2xl border-l-2 border-accent bg-accent/[0.06] p-5 pl-6">
            <h3 className="font-sans text-xs uppercase tracking-widest accent mb-2">
              Note on the formalization
            </h3>
            <MathText
              html={r.formalizationNotes}
              className="font-serif text-[0.98rem] text-ink-soft leading-relaxed"
            />
          </div>
        )}

        {/* prev / next */}
        <nav className="mt-12 grid sm:grid-cols-2 gap-4">
          {prev ? (
            <Link to={`/result/${prev.id}`} className="nav-card text-left">
              <span className="text-ink-faint text-xs font-sans">← Previous</span>
              <span className="font-display font-medium">{prev.title}</span>
            </Link>
          ) : <span />}
          {next ? (
            <Link to={`/result/${next.id}`} className="nav-card text-right sm:items-end">
              <span className="text-ink-faint text-xs font-sans">Next →</span>
              <span className="font-display font-medium">{next.title}</span>
            </Link>
          ) : <span />}
        </nav>
      </section>
    </div>
  );
}

function PaneHeader({
  label,
  sub,
  mono,
}: {
  label: string;
  sub: string;
  mono?: boolean;
}) {
  return (
    <div className="flex items-center justify-between px-5 py-3 border-b hairline bg-parchment/40">
      <span className="font-sans text-xs uppercase tracking-widest text-ink-faint">
        {label}
      </span>
      <span
        className={`text-xs text-ink-faint truncate max-w-[55%] ${
          mono ? "font-mono" : "font-sans"
        }`}
      >
        {sub}
      </span>
    </div>
  );
}
